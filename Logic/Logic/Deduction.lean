import Logic.Logic.System
import Logic.Logic.Axioms
import Logic.Logic.HilbertStyle.Basic

namespace LO

namespace DeductionSystem

variable {F : Type*} [LogicalConnective F]

structure Rule (F) where
  antecedents : List F
  consequence  : F

abbrev Rules (F) := Set (Rule F)

inductive Deduction (𝓡 : Rules F) : F → Type _
  | rule {rl} : rl ∈ 𝓡 → (∀ {p}, p ∈ rl.antecedents → Deduction 𝓡 p) → Deduction 𝓡 rl.consequence

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


namespace InferenceRules

abbrev Init (Ax : Set F) : Rules F := { ⟨[], p⟩ | (p ∈ Ax) }
postfix:max "ⁱ" => Init

abbrev ModusPonens : Rules F := { ⟨[p, p ⟶ q], q⟩ | (p) (q) }
notation "⟮MP⟯" => ModusPonens

end InferenceRules

infixr:20 "⊕" => (· ∪ ·)

abbrev MinimalPropositional : Rules F := ⟮⊤⟯ⁱ ⊕ ⟮⟶₁⟯ⁱ ⊕ ⟮⟶₂⟯ⁱ ⊕ ⟮⋏E₁⟯ⁱ ⊕ ⟮⋏E₂⟯ⁱ ⊕ ⟮⋏I⟯ⁱ ⊕ ⟮⋎E⟯ⁱ ⊕ ⟮⋎I₁⟯ⁱ ⊕ ⟮⋎I₂⟯ⁱ ⊕ ⟮~⟯ⁱ ⊕ ⟮MP⟯
notation "𝐦𝐏𝐋" => MinimalPropositional

abbrev IntuitionisticPropositional : Rules F := 𝐦𝐏𝐋 ⊕ ⟮EFQ⟯ⁱ
notation "𝐢𝐏𝐋" => IntuitionisticPropositional

abbrev ClassicalPropositional : Rules F := 𝐦𝐏𝐋 ⊕ ⟮DNE⟯ⁱ
notation "𝐜𝐏𝐋" => ClassicalPropositional


open LO.System

variable {𝓡 : Rules F}

instance instModusPonens (h : ⟮MP⟯ ⊆ 𝓡) : ModusPonens 𝓡 where
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

instance instHasNegEquiv (h : ⟮~⟯ⁱ ⊆ 𝓡) : System.NegationEquiv 𝓡 where
  neg_equiv := by intro p; exact Deduction.rule (show ⟨[], Axioms.NegEquiv p⟩ ∈ 𝓡 by aesop) (by intros; simp_all);

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
  neg_equiv := instHasNegEquiv (by aesop) |>.neg_equiv;

instance : System.Minimal (𝐦𝐏𝐋 : Rules F) := instMinimal (by rfl)


instance instIntuitionistic (h : 𝐢𝐏𝐋 ⊆ 𝓡) : System.Intuitionistic 𝓡 := by
  have : System.Minimal 𝓡 := instMinimal (by aesop);
  have : System.HasEFQ 𝓡 := instHasEFQ (by aesop);
  exact ⟨⟩;

instance : System.Intuitionistic (𝐢𝐏𝐋 : Rules F) := instIntuitionistic (by rfl)


instance instClassical (h : 𝐜𝐏𝐋 ⊆ 𝓡) : System.Classical 𝓡 := by
  have : System.Minimal 𝓡 := instMinimal (by aesop);
  have : System.HasDNE 𝓡 := instHasDNE (by aesop);
  exact ⟨⟩;

instance : System.Classical (𝐜𝐏𝐋 : Rules F) := instClassical (by rfl)

noncomputable def MinimalPropositional.inducition!
  {motive : (p : F) → 𝐦𝐏𝐋 ⊢! p → Prop}
  (mdp    : ∀ {p q}, {hpq : 𝐦𝐏𝐋 ⊢! p ⟶ q} → {hp : 𝐦𝐏𝐋 ⊢! p} → motive (p ⟶ q) hpq → motive p hp → motive q (hpq ⨀ hp))
  (verum    : motive ⊤ verum!)
  (imply₁   : ∀ {p q}, motive (p ⟶ q ⟶ p) $ imply₁!)
  (Imply₂   : ∀ {p q r}, motive ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) $ imply₂!)
  (andElim₁ : ∀ {p q}, motive (p ⋏ q ⟶ p) $ and₁!)
  (andElim₂ : ∀ {p q}, motive (p ⋏ q ⟶ q) $ and₂!)
  (andInst₁ : ∀ {p q}, motive (p ⟶ q ⟶ p ⋏ q) $ and₃!)
  (orInst₁  : ∀ {p q}, motive (p ⟶ p ⋎ q) $ or₁!)
  (OrInst₂  : ∀ {p q}, motive (q ⟶ p ⋎ q) $ or₂!)
  (orElim   : ∀ {p q r}, motive ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)) $ or₃!)
  (negEquiv : ∀ {p}, motive (~p ⟷ (p ⟶ ⊥)) $ neg_equiv!)
  : ∀ {p}, (d : 𝐦𝐏𝐋 ⊢! p) → motive p d := by
  intro p d;
  induction d using Deduction.inducition! with
  | rule rl hrl hant ih =>
    rcases hrl with (hVerum | hImply₁ | hImply₂ | hAndElim₁ | hAndElim₂ | hAndInst | hOrElim | hOrInst₁ | hOrInst₂ | hNegEquiv | hMP)
    . obtain ⟨_, ⟨_⟩, _⟩ := hVerum; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];
    . obtain ⟨_, ⟨_, _, _⟩, _⟩ := hImply₁; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];
    . obtain ⟨_, ⟨_, _, _, _⟩, _⟩ := hImply₂; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];
    . obtain ⟨_, ⟨_, _, _⟩, _⟩ := hAndElim₁; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];
    . obtain ⟨_, ⟨_, _, _⟩, _⟩ := hAndElim₂; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];
    . obtain ⟨_, ⟨_, _, _⟩, _⟩ := hAndInst; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];
    . obtain ⟨_, ⟨_, _, _, _⟩, _⟩ := hOrElim; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];
    . obtain ⟨_, ⟨_, _, _⟩, _⟩ := hOrInst₁; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];
    . obtain ⟨_, ⟨_, _, _⟩, _⟩ := hOrInst₂; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];
    . obtain ⟨_, ⟨_, _, _⟩, _⟩ := hNegEquiv; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];
    . obtain ⟨p, q, _⟩ := hMP; subst_vars;
      have ihp := @ih p (by simp);
      have ihpq := @ih (p ⟶ q) (by simp);
      exact mdp ihpq ihp;

noncomputable def induction_IntuitionisticPropositional!
  {motive : (p : F) → 𝐢𝐏𝐋 ⊢! p → Prop}
  (mdp    : ∀ {p q}, {hpq : 𝐢𝐏𝐋 ⊢! p ⟶ q} → {hp : 𝐢𝐏𝐋 ⊢! p} → motive (p ⟶ q) hpq → motive p hp → motive q (hpq ⨀ hp))
  (verum    : motive ⊤ verum!)
  (imply₁   : ∀ {p q}, motive (p ⟶ q ⟶ p) $ imply₁!)
  (Imply₂   : ∀ {p q r}, motive ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) $ imply₂!)
  (andElim₁ : ∀ {p q}, motive (p ⋏ q ⟶ p) $ and₁!)
  (andElim₂ : ∀ {p q}, motive (p ⋏ q ⟶ q) $ and₂!)
  (andInst₁ : ∀ {p q}, motive (p ⟶ q ⟶ p ⋏ q) $ and₃!)
  (orInst₁  : ∀ {p q}, motive (p ⟶ p ⋎ q) $ or₁!)
  (OrInst₂  : ∀ {p q}, motive (q ⟶ p ⋎ q) $ or₂!)
  (orElim   : ∀ {p q r}, motive ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)) $ or₃!)
  (negEquiv : ∀ {p}, motive (~p ⟷ (p ⟶ ⊥)) $ neg_equiv!)
  (efq      : ∀ {p}, motive (⊥ ⟶ p) $ efq!)
  : ∀ {p}, (d : 𝐢𝐏𝐋 ⊢! p) → motive p d := by
  intro p d;
  induction d using Deduction.inducition! with
  | rule rl hrl hant ih =>
    rcases hrl with (hVerum | hImply₁ | hImply₂ | hAndElim₁ | hAndElim₂ | hAndInst | hOrElim | hOrInst₁ | hOrInst₂ | hNegEquiv | hMP) | hEFQ
    . obtain ⟨_, ⟨_⟩, _⟩ := hVerum; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];
    . obtain ⟨_, ⟨_, _, _⟩, _⟩ := hImply₁; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];
    . obtain ⟨_, ⟨_, _, _, _⟩, _⟩ := hImply₂; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];
    . obtain ⟨_, ⟨_, _, _⟩, _⟩ := hAndElim₁; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];
    . obtain ⟨_, ⟨_, _, _⟩, _⟩ := hAndElim₂; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];
    . obtain ⟨_, ⟨_, _, _⟩, _⟩ := hAndInst; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];
    . obtain ⟨_, ⟨_, _, _, _⟩, _⟩ := hOrElim; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];
    . obtain ⟨_, ⟨_, _, _⟩, _⟩ := hOrInst₁; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];
    . obtain ⟨_, ⟨_, _, _⟩, _⟩ := hOrInst₂; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];
    . obtain ⟨_, ⟨_, _, _⟩, _⟩ := hNegEquiv; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];
    . obtain ⟨p, q, _⟩ := hMP; subst_vars;
      have ihp := @ih p (by simp);
      have ihpq := @ih (p ⟶ q) (by simp);
      exact mdp ihpq ihp;
    . obtain ⟨_, ⟨_⟩, _⟩ := hEFQ; subst_vars; simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true];



end DeductionSystem

end LO
