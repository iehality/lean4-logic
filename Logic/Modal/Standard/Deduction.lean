import Logic.Modal.Standard.Formula
import Logic.Modal.Standard.System

namespace LO.Modal.Standard

variable {α : Type*} [DecidableEq α]

/-- instance of inference rule -/
structure InferenceRule (α : Type*) where
  antecedents : List (Formula α)
  /--
  Empty antecedent rule can be simply regarded as axiom rule.
  However, union of all these rules including to `DeductionParameter.rules` would be too complex for implementation and induction,
  so more than one antecedent is required.
  -/
  antecedents_nonempty : antecedents ≠ [] := by simp
  consequence : Formula α

abbrev InferenceRules (α : Type*) := Set (InferenceRule α)

abbrev Necessitation {α} : InferenceRules α := { { antecedents := [p], consequence := □p} | (p) }
notation "⟮Nec⟯" => Necessitation

abbrev LoebRule {α} : InferenceRules α := { { antecedents := [□p ⟶ p], consequence := p} | (p) }
notation "⟮Loeb⟯" => LoebRule

abbrev HenkinRule {α} : InferenceRules α := { { antecedents := [□p ⟷ p], consequence := p }| (p) }
notation "⟮Henkin⟯" => HenkinRule

abbrev RosserRule {α} : InferenceRules α := { { antecedents := [~p], consequence := ~(□p) } | (p) }
notation "⟮Rosser⟯" => RosserRule

abbrev RosserBoxRule {α} : InferenceRules α := { { antecedents := [~(□p)], consequence := ~(□□p) } | (p) }
notation "⟮Rosser□⟯" => RosserBoxRule

structure DeductionParameter (α : Type*) where
  axioms : AxiomSet α
  rules : InferenceRules α

namespace DeductionParameter

notation "Ax(" 𝓓 ")" => DeductionParameter.axioms 𝓓
notation "Rl(" 𝓓 ")" => DeductionParameter.rules 𝓓

end DeductionParameter

inductive Deduction (𝓓 : DeductionParameter α) : (Formula α) → Type _
  | maxm {p}     : p ∈ Ax(𝓓) → Deduction 𝓓 p
  | rule {rl}    : rl ∈ Rl(𝓓) → (∀ {p}, p ∈ rl.antecedents → Deduction 𝓓 p) → Deduction 𝓓 rl.consequence
  | mdp {p q}    : Deduction 𝓓 (p ⟶ q) → Deduction 𝓓 p → Deduction 𝓓 q
  | verum        : Deduction 𝓓 $ Axioms.Verum
  | imply₁ p q   : Deduction 𝓓 $ Axioms.Imply₁ p q
  | imply₂ p q r : Deduction 𝓓 $ Axioms.Imply₂ p q r
  | and₁ p q     : Deduction 𝓓 $ Axioms.AndElim₁ p q
  | and₂ p q     : Deduction 𝓓 $ Axioms.AndElim₂ p q
  | and₃ p q     : Deduction 𝓓 $ Axioms.AndInst p q
  | or₁ p q      : Deduction 𝓓 $ Axioms.OrInst₁ p q
  | or₂ p q      : Deduction 𝓓 $ Axioms.OrInst₂ p q
  | or₃ p q r    : Deduction 𝓓 $ Axioms.OrElim p q r
  | dne p        : Deduction 𝓓 $ Axioms.DNE p

namespace Deduction

open DeductionParameter

instance : System (Formula α) (DeductionParameter α) := ⟨Deduction⟩

variable {𝓓 𝓓₁ 𝓓₂ : DeductionParameter α}

instance : System.Minimal 𝓓 where
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

instance : System.Classical 𝓓 where
  dne := dne

lemma maxm! {p} (h : p ∈ 𝓓.axioms) : 𝓓 ⊢! p := ⟨maxm h⟩

end Deduction


namespace DeductionParameter

open System Deduction

class HasNecessitation (𝓓 : DeductionParameter α) where
  has_necessitation : ⟮Nec⟯ ⊆ Rl(𝓓) := by aesop

instance [HasNecessitation 𝓓] : System.Necessitation 𝓓 where
  nec := @λ p d => rule (show { antecedents := [p], consequence := □p } ∈ Rl(𝓓) by apply HasNecessitation.has_necessitation; simp_all) (by aesop);


class HasLoebRule (𝓓 : DeductionParameter α) where
  has_loeb : ⟮Loeb⟯ ⊆ Rl(𝓓) := by aesop

instance [HasLoebRule 𝓓] : System.LoebRule 𝓓 where
  loeb := @λ p d => rule (show { antecedents := [□p ⟶ p], consequence := p } ∈ Rl(𝓓) by apply HasLoebRule.has_loeb; simp_all) (by aesop);


class HasHenkinRule (𝓓 : DeductionParameter α) where
  has_henkin : ⟮Henkin⟯ ⊆ Rl(𝓓) := by aesop

instance [HasHenkinRule 𝓓] : System.HenkinRule 𝓓 where
  henkin := @λ p d => rule (show { antecedents := [□p ⟷ p], consequence := p } ∈ Rl(𝓓) by apply HasHenkinRule.has_henkin; simp_all) (by aesop);


class HasNecOnly (𝓓 : DeductionParameter α) where
  has_necessitation_only : Rl(𝓓) = ⟮Nec⟯ := by rfl

instance [h : HasNecOnly 𝓓] : 𝓓.HasNecessitation where
  has_necessitation := by rw [h.has_necessitation_only]

class HasAxiomK (𝓓 : DeductionParameter α) where
  has_axiomK : 𝗞 ⊆ Ax(𝓓) := by aesop

instance [HasAxiomK 𝓓] : System.HasAxiomK 𝓓 where
  K _ _ := maxm (by apply HasAxiomK.has_axiomK; simp_all)

class IsNormal (𝓓 : DeductionParameter α) extends 𝓓.HasNecOnly, 𝓓.HasAxiomK where


end DeductionParameter

namespace Deduction

open DeductionParameter

variable {𝓓 : DeductionParameter α}

noncomputable def inducition!
  {motive  : (p : Formula α) → 𝓓 ⊢! p → Sort*}
  (hRules  : (r : InferenceRule α) → (hr : r ∈ Rl(𝓓)) →
             (hant : ∀ {p}, p ∈ r.antecedents → 𝓓 ⊢! p) →
             (ih : ∀ {p}, (hp : p ∈ r.antecedents) →
             motive p (hant hp)) → motive r.consequence ⟨rule hr (λ hp => (hant hp).some)⟩)
  (hMaxm     : ∀ {p}, (h : p ∈ Ax(𝓓)) → motive p ⟨maxm h⟩)
  (hMdp      : ∀ {p q}, {hpq : 𝓓 ⊢! p ⟶ q} → {hp : 𝓓 ⊢! p} → motive (p ⟶ q) hpq → motive p hp → motive q ⟨mdp hpq.some hp.some⟩)
  (hVerum    : motive ⊤ ⟨verum⟩)
  (hImply₁   : ∀ {p q}, motive (p ⟶ q ⟶ p) $ ⟨imply₁ p q⟩)
  (hImply₂   : ∀ {p q r}, motive ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) $ ⟨imply₂ p q r⟩)
  (hAndElim₁ : ∀ {p q}, motive (p ⋏ q ⟶ p) $ ⟨and₁ p q⟩)
  (hAndElim₂ : ∀ {p q}, motive (p ⋏ q ⟶ q) $ ⟨and₂ p q⟩)
  (hAndInst  : ∀ {p q}, motive (p ⟶ q ⟶ p ⋏ q) $ ⟨and₃ p q⟩)
  (hOrInst₁  : ∀ {p q}, motive (p ⟶ p ⋎ q) $ ⟨or₁ p q⟩)
  (hOrInst₂  : ∀ {p q}, motive (q ⟶ p ⋎ q) $ ⟨or₂ p q⟩)
  (hOrElim   : ∀ {p q r}, motive ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)) $ ⟨or₃ p q r⟩)
  (hDne      : ∀ {p}, motive (~~p ⟶ p) $ ⟨dne p⟩)
  : ∀ {p}, (d : 𝓓 ⊢! p) → motive p d := by
  intro p d;
  induction d.some with
  | maxm h => exact hMaxm h
  | mdp hpq hp ihpq ihp => exact hMdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | rule hr h ih => apply hRules _ hr; intro p hp; exact ih hp ⟨h hp⟩;
  | _ => aesop

/-- Useful induction for normal modal logic (because its inference rule is necessitation only) -/
noncomputable def inducition_with_necOnly! [𝓓.HasNecOnly]
  {motive  : (p : Formula α) → 𝓓 ⊢! p → Prop}
  (hMaxm   : ∀ {p}, (h : p ∈ Ax(𝓓)) → motive p ⟨maxm h⟩)
  (hMdp    : ∀ {p q}, {hpq : 𝓓 ⊢! p ⟶ q} → {hp : 𝓓 ⊢! p} → motive (p ⟶ q) hpq → motive p hp → motive q (hpq ⨀ hp))
  (hNec    : ∀ {p}, {hp : 𝓓 ⊢! p} → (ihp : motive p hp) → motive (□p) (System.nec! hp))
  (hVerum    : motive ⊤ ⟨verum⟩)
  (hImply₁   : ∀ {p q}, motive (p ⟶ q ⟶ p) $ ⟨imply₁ p q⟩)
  (hImply₂   : ∀ {p q r}, motive ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) $ ⟨imply₂ p q r⟩)
  (hAndElim₁ : ∀ {p q}, motive (p ⋏ q ⟶ p) $ ⟨and₁ p q⟩)
  (hAndElim₂ : ∀ {p q}, motive (p ⋏ q ⟶ q) $ ⟨and₂ p q⟩)
  (hAndInst  : ∀ {p q}, motive (p ⟶ q ⟶ p ⋏ q) $ ⟨and₃ p q⟩)
  (hOrInst₁  : ∀ {p q}, motive (p ⟶ p ⋎ q) $ ⟨or₁ p q⟩)
  (hOrInst₂  : ∀ {p q}, motive (q ⟶ p ⋎ q) $ ⟨or₂ p q⟩)
  (hOrElim   : ∀ {p q r}, motive ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)) $ ⟨or₃ p q r⟩)
  (hDne      : ∀ {p}, motive (~~p ⟶ p) $ ⟨dne p⟩)
  : ∀ {p}, (d : 𝓓 ⊢! p) → motive p d := by
  intro p d;
  induction d using Deduction.inducition! with
  | hMaxm h => exact hMaxm h
  | hMdp ihpq ihp => exact hMdp (ihpq) (ihp);
  | hRules rl hrl hant ih =>
    rw [HasNecOnly.has_necessitation_only] at hrl;
    obtain ⟨p, e⟩ := hrl; subst e;
    exact @hNec p (hant (by simp)) $ ih (by simp);
  | hVerum => exact hVerum
  | hImply₁ => exact hImply₁
  | hImply₂ => exact hImply₂
  | hAndElim₁ => exact hAndElim₁
  | hAndElim₂ => exact hAndElim₂
  | hAndInst => exact hAndInst
  | hOrInst₁ => exact hOrInst₁
  | hOrInst₂ => exact hOrInst₂
  | hOrElim => exact hOrElim
  | hDne => exact hDne

end Deduction


namespace DeductionParameter

open DeductionParameter

abbrev theory (𝓓 : DeductionParameter α) := System.theory 𝓓

protected abbrev K : DeductionParameter α where
  axioms := 𝗞
  rules := ⟮Nec⟯
notation "𝐊" => DeductionParameter.K
instance : 𝐊.IsNormal (α := α) where


section Normal

abbrev Normal (Ax : AxiomSet α) : DeductionParameter α where
  axioms := 𝗞 ∪ Ax
  rules := ⟮Nec⟯
instance : IsNormal (α := α) (Normal Ax) where
prefix:max "𝝂" => Normal

namespace Normal

variable {Ax : AxiomSet α}

lemma isK : 𝐊 = Normal (α := α) 𝗞 := by aesop;

lemma def_ax : Ax(𝝂Ax) = (𝗞 ∪ Ax) := by simp;

lemma maxm! (h : p ∈ Ax) : 𝝂Ax ⊢! p := ⟨Deduction.maxm (by simp [def_ax]; right; assumption)⟩

end Normal

protected abbrev KT : DeductionParameter α := 𝝂𝗧
notation "𝐊𝐓" => DeductionParameter.KT


protected abbrev KD : DeductionParameter α := 𝝂𝗗
notation "𝐊𝐃" => DeductionParameter.KD


protected abbrev K4 : DeductionParameter α := 𝝂𝟰
notation "𝐊𝟒" => DeductionParameter.K4
instance : System.K4 (𝐊𝟒 : DeductionParameter α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)


protected abbrev K5 : DeductionParameter α := 𝝂𝟱
notation "𝐊𝟓" => DeductionParameter.K5


protected abbrev S4 : DeductionParameter α := 𝝂(𝗧 ∪ 𝟰)
notation "𝐒𝟒" => DeductionParameter.S4
instance : System.S4 (𝐒𝟒 : DeductionParameter α) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)


protected abbrev S5 : DeductionParameter α := 𝝂(𝗧 ∪ 𝟱)
notation "𝐒𝟓" => DeductionParameter.S5
instance : IsNormal (α := α) 𝐒𝟓 where


protected abbrev KT4B : DeductionParameter α := 𝝂(𝗧 ∪ 𝟰 ∪ 𝗕)
notation "𝐊𝐓𝟒𝐁" => DeductionParameter.KT4B


protected abbrev S4Dot2 : DeductionParameter α := 𝝂(𝗧 ∪ 𝟰 ∪ .𝟮)
notation "𝐒𝟒.𝟐" => DeductionParameter.S4Dot2


protected abbrev S4Dot3 : DeductionParameter α := 𝝂(𝗧 ∪ 𝟰 ∪ .𝟯)
notation "𝐒𝟒.𝟑" => DeductionParameter.S4Dot3


protected abbrev S4Grz : DeductionParameter α := 𝝂(𝗧 ∪ 𝟰 ∪ 𝗚𝗿𝘇)
notation "𝐒𝟒𝐆𝐫𝐳" => DeductionParameter.S4Grz


protected abbrev Triv : DeductionParameter α := 𝝂(𝗧 ∪ 𝗧𝗰)
notation "𝐓𝐫𝐢𝐯" => DeductionParameter.Triv
instance : System.Triv (𝐓𝐫𝐢𝐯 : DeductionParameter α) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  Tc _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)


protected abbrev Ver : DeductionParameter α := 𝝂(𝗩𝗲𝗿)
notation "𝐕𝐞𝐫" => DeductionParameter.Ver
instance : System.Ver (𝐕𝐞𝐫 : DeductionParameter α) where
  Ver _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)


protected abbrev GL : DeductionParameter α := 𝝂(𝗟)
notation "𝐆𝐋" => DeductionParameter.GL
instance : System.GL (𝐆𝐋 : DeductionParameter α) where
  L _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)


protected abbrev K4H : DeductionParameter α := 𝝂(𝟰 ∪ 𝗛)
notation "𝐊𝟒𝐇" => DeductionParameter.K4H
instance : System.K4H (𝐊𝟒𝐇 : DeductionParameter α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  H _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

end Normal


section GLAlternative

protected abbrev K4Loeb : DeductionParameter α where
  axioms := 𝗞 ∪ 𝟰
  rules :=  ⟮Nec⟯ ∪ ⟮Loeb⟯
notation "𝐊𝟒(𝐋)" => DeductionParameter.K4Loeb
instance : 𝐊𝟒(𝐋).HasAxiomK (α := α) where
instance : 𝐊𝟒(𝐋).HasNecessitation (α := α) where
instance : 𝐊𝟒(𝐋).HasLoebRule (α := α) where
instance : System.K4Loeb (𝐊𝟒(𝐋) : DeductionParameter α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)


protected abbrev K4Henkin : DeductionParameter α where
  axioms := 𝗞 ∪ 𝟰
  rules := ⟮Nec⟯ ∪ ⟮Henkin⟯
notation "𝐊𝟒(𝐇)" => DeductionParameter.K4Henkin
instance : 𝐊𝟒(𝐇).HasAxiomK (α := α)  where
instance : 𝐊𝟒(𝐇).HasNecessitation (α := α) where
instance : 𝐊𝟒(𝐇).HasHenkinRule (α := α) where
instance : System.K4Henkin (𝐊𝟒(𝐇) : DeductionParameter α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

end GLAlternative


section PLoN

/-- Logic of Pure Necessitation -/
protected abbrev N : DeductionParameter α where
  axioms := ∅
  rules := ⟮Nec⟯
notation "𝐍" => DeductionParameter.N
instance : 𝐍.HasNecOnly (α := α) where

end PLoN

protected abbrev N4 : DeductionParameter α where
  axioms := 𝟰
  rules := ⟮Nec⟯
notation "𝐍𝟒" => DeductionParameter.N4
instance : HasNecOnly (α := α) 𝐍𝟒 where
instance : System.HasAxiomFour (𝐍𝟒 : DeductionParameter α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev NRosser : DeductionParameter α where
  axioms := ∅
  rules := ⟮Nec⟯ ∪ ⟮Rosser⟯
notation "𝐍(𝐑)" => DeductionParameter.NRosser
instance : 𝐍(𝐑).HasNecessitation (α := α) where

protected abbrev N4Rosser : DeductionParameter α where
  axioms := 𝟰
  rules := ⟮Nec⟯ ∪ ⟮Rosser□⟯
notation "𝐍𝟒(𝐑)" => DeductionParameter.N4Rosser
instance : 𝐍𝟒(𝐑).HasNecessitation (α := α) where
instance : System.HasAxiomFour (𝐍𝟒(𝐑) : DeductionParameter α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

end DeductionParameter

open System

macro_rules | `(tactic| trivial) => `(tactic|
    first
    | apply verum!
    | apply imply₁!
    | apply imply₁!
    | apply imply₂!
    | apply and₁!
    | apply and₂!
    | apply and₃!
    | apply or₁!
    | apply or₂!
    | apply or₃!
  )

macro_rules | `(tactic| trivial) => `(tactic | apply dne!)

section Reducible

lemma normal_reducible {𝓓₁ 𝓓₂ : DeductionParameter α} [𝓓₁.IsNormal] [𝓓₂.IsNormal]
  (hMaxm : ∀ {p : Formula α}, p ∈ Ax(𝓓₁) → 𝓓₂ ⊢! p)
  : 𝓓₁ ≤ₛ 𝓓₂ := by
  apply System.reducible_iff.mpr;
  intro p h;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm hp => exact hMaxm hp;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hNec ihp => exact nec! ihp;
  | _ => trivial;


lemma normal_reducible_subset {𝓓₁ 𝓓₂ : DeductionParameter α} [𝓓₁.IsNormal] [𝓓₂.IsNormal]
  (hSubset : Ax(𝓓₁) ⊆ Ax(𝓓₂) := by intro; aesop;)
  : 𝓓₁ ≤ₛ 𝓓₂ := by
  apply normal_reducible;
  intro p hp;
  exact ⟨Deduction.maxm $ hSubset hp⟩;

lemma reducible_K_KT : (𝐊 : DeductionParameter α) ≤ₛ 𝐊𝐓 := by exact normal_reducible_subset;

lemma reducible_K_KD : (𝐊 : DeductionParameter α) ≤ₛ 𝐊𝐃 := by exact normal_reducible_subset;

lemma reducible_KT_S4 : (𝐊𝐓 : DeductionParameter α) ≤ₛ 𝐒𝟒 := by exact normal_reducible_subset;

lemma reducible_K4_S4 : (𝐊𝟒 : DeductionParameter α) ≤ₛ 𝐒𝟒 := by exact normal_reducible_subset;

lemma reducible_S4_S4Dot2 : (𝐒𝟒 : DeductionParameter α) ≤ₛ 𝐒𝟒.𝟐 := by exact normal_reducible_subset

lemma reducible_S4_S4Dot3 : (𝐒𝟒 : DeductionParameter α) ≤ₛ 𝐒𝟒.𝟑 := by exact normal_reducible_subset

lemma reducible_S4_S4Grz : (𝐒𝟒 : DeductionParameter α) ≤ₛ 𝐒𝟒𝐆𝐫𝐳 := by exact normal_reducible_subset

lemma reducible_K_GL : (𝐊 : DeductionParameter α) ≤ₛ 𝐆𝐋 := by exact normal_reducible_subset

lemma reducible_K4_Triv : (𝐊𝟒 : DeductionParameter α) ≤ₛ 𝐓𝐫𝐢𝐯 := by
  apply normal_reducible;
  intro p hp;
  rcases hp with (hK | hFour)
  . obtain ⟨_, _, e⟩ := hK; subst_vars; exact axiomK!;
  . obtain ⟨_, _, e⟩ := hFour; subst_vars; exact axiomFour!;

lemma reducible_K4_GL : (𝐊𝟒 : DeductionParameter α) ≤ₛ 𝐆𝐋 := by
  apply normal_reducible;
  intro p hp;
  rcases hp with (hK | hFour)
  . obtain ⟨_, _, e⟩ := hK; subst_vars; exact axiomK!;
  . obtain ⟨_, _, e⟩ := hFour; subst_vars; exact axiomFour!;

-- Macintyre & Simmons (1973)
-- 𝐆𝐋 =ₛ 𝐊𝟒(𝐋) =ₛ 𝐊𝟒(𝐇) =ₛ 𝐊𝟒𝐇
section GL

lemma reducible_GL_K4Loeb : (𝐆𝐋 : DeductionParameter α) ≤ₛ 𝐊𝟒(𝐋) := by
  apply System.reducible_iff.mpr;
  intro p h;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm hp =>
    rcases hp with (hK | hL)
    . obtain ⟨_, _, e⟩ := hK; subst_vars; exact axiomK!;
    . obtain ⟨_, e⟩ := hL; subst_vars; exact axiomL!;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hNec ihp => exact nec! ihp;
  | _ => trivial;

lemma reducible_K4Loeb_K4Henkin : (𝐊𝟒(𝐋) : DeductionParameter α) ≤ₛ 𝐊𝟒(𝐇) := by
  apply System.reducible_iff.mpr;
  intro p h;
  induction h using Deduction.inducition! with
  | hMaxm hp =>
    rcases hp with (hK | hFour)
    . obtain ⟨_, _, e⟩ := hK; subst_vars; exact axiomK!;
    . obtain ⟨_, e⟩ := hFour; subst_vars; exact axiomFour!;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hRules rl hrl hant ihp =>
    rcases hrl with (hNec | hLoeb);
    . obtain ⟨p, e⟩ := hNec; subst_vars; exact nec! $ ihp (by aesop);
    . obtain ⟨p, e⟩ := hLoeb; subst_vars; exact loeb! $ ihp (by aesop);
  | _ => trivial;

lemma reducible_K4Henkin_K4H : (𝐊𝟒(𝐇) : DeductionParameter α) ≤ₛ 𝐊𝟒𝐇 := by
  apply System.reducible_iff.mpr;
  intro p h;
  induction h using Deduction.inducition! with
  | hMaxm hp =>
    rcases hp with (hK | hFour)
    . obtain ⟨_, _, e⟩ := hK; subst_vars; exact axiomK!;
    . obtain ⟨_, e⟩ := hFour; subst_vars; exact axiomFour!;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hRules rl hrl hant ihp =>
    rcases hrl with (hNec | hHenkin);
    . obtain ⟨p, e⟩ := hNec; subst_vars; exact nec! $ ihp (by aesop);
    . obtain ⟨p, e⟩ := hHenkin; subst_vars; exact henkin! $ ihp (by aesop);
  | _ => trivial;

lemma reducible_K4Henkin_GL : (𝐊𝟒𝐇 : DeductionParameter α) ≤ₛ 𝐆𝐋 := by
  apply normal_reducible;
  intro p hp;
  rcases hp with hK | hFour | hH
  . obtain ⟨_, _, e⟩ := hK; subst_vars; exact axiomK!;
  . obtain ⟨_, _, e⟩ := hFour; subst_vars; exact axiomFour!;
  . obtain ⟨_, _, e⟩ := hH; subst_vars; exact axiomH!;

lemma equivalent_GL_K4Loeb : (𝐆𝐋 : DeductionParameter α) =ₛ 𝐊𝟒(𝐋) := by
  apply Equiv.antisymm_iff.mpr;
  constructor;
  . exact reducible_GL_K4Loeb;
  . exact Reducible.trans (reducible_K4Loeb_K4Henkin) $ Reducible.trans reducible_K4Henkin_K4H reducible_K4Henkin_GL

end GL

end Reducible

end LO.Modal.Standard
