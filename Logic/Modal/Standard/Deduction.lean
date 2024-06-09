import Logic.Modal.Standard.Formula
import Logic.Modal.Standard.HilbertStyle

namespace LO.Modal.Standard

variable {α : Type*} [DecidableEq α]

structure DeductionParameterRules where
  nec : Bool
  loeb : Bool
  henkin : Bool

namespace DeductionParameterRules

abbrev le (R₁ R₂ : DeductionParameterRules) : Prop :=
  R₁.nec ≤ R₂.nec ∧
  R₁.loeb ≤ R₂.loeb ∧
  R₁.henkin ≤ R₂.henkin

instance : LE DeductionParameterRules where
  le R₁ R₂ :=
    R₁.nec ≤ R₂.nec ∧
    R₁.loeb ≤ R₂.loeb ∧
    R₁.henkin ≤ R₂.henkin

variable {R₁ R₂ : DeductionParameterRules} (h : R₁ ≤ R₂ := by simpa)

@[simp] lemma nec_le (hNec : R₁.nec = true) : R₂.nec = true := by apply h.1; assumption;
@[simp] lemma loeb_le (hLoeb : R₁.loeb = true) : R₂.loeb = true := by apply h.2.1; assumption;
@[simp] lemma henkin_le (hHenkin : R₁.henkin = true) : R₂.henkin = true := by apply h.2.2; assumption;

end DeductionParameterRules

/--
  Parameter for deduction system.
-/
structure DeductionParameter (α) where
  axiomSet : AxiomSet α
  rules : DeductionParameterRules
notation "Ax(" 𝓓 ")" => DeductionParameter.axiomSet 𝓓

namespace DeductionParameter

variable (𝓓 𝓓₁ 𝓓₂ : DeductionParameter α)

class HasNec where
  has_nec : 𝓓.rules.nec = true := by rfl

class HasLoebRule where
  has_loeb : 𝓓.rules.loeb = true := by rfl

class HasHenkinRule where
  has_henkin : 𝓓.rules.henkin = true := by rfl

class HasNecOnly extends HasNec 𝓓 where
  not_has_loeb : 𝓓.rules.loeb = false := by rfl
  not_has_henkin : 𝓓.rules.henkin = false := by rfl

class IncludeK where
  include_K : 𝗞 ⊆ Ax(𝓓) := by intro; aesop;

/--
  Deduction system of `L` is normal modal 𝓓ogic.
-/
class Normal extends HasNecOnly 𝓓, IncludeK 𝓓 where

end DeductionParameter


inductive Deduction (𝓓 : DeductionParameter α) : (Formula α) → Type _
  | maxm {p}     : p ∈ Ax(𝓓) → Deduction 𝓓 p
  | mdp {p q}    : Deduction 𝓓 (p ⟶ q) → Deduction 𝓓 p → Deduction 𝓓 q
  | nec {p}      : (𝓓.rules.nec = true) → Deduction 𝓓 p → Deduction 𝓓 (□p)
  | loeb {p}     : (𝓓.rules.loeb = true) → Deduction 𝓓 (□p ⟶ p) → Deduction 𝓓 p
  | henkin {p}   : (𝓓.rules.henkin = true) → Deduction 𝓓 (□p ⟷ p) → Deduction 𝓓 p
  | verum        : Deduction 𝓓 ⊤
  | imply₁ p q   : Deduction 𝓓 (p ⟶ q ⟶ p)
  | imply₂ p q r : Deduction 𝓓 ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
  | conj₁ p q    : Deduction 𝓓 (p ⋏ q ⟶ p)
  | conj₂ p q    : Deduction 𝓓 (p ⋏ q ⟶ q)
  | conj₃ p q    : Deduction 𝓓 (p ⟶ q ⟶ p ⋏ q)
  | disj₁ p q    : Deduction 𝓓 (p ⟶ p ⋎ q)
  | disj₂ p q    : Deduction 𝓓 (q ⟶ p ⋎ q)
  | disj₃ p q r  : Deduction 𝓓 ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r))
  | dne p        : Deduction 𝓓 (~~p ⟶ p)

namespace Deduction

open DeductionParameter

instance : System (Formula α) (DeductionParameter α) := ⟨Deduction⟩

variable {𝓓 𝓓₁ 𝓓₂ : DeductionParameter α}

instance : System.Classical 𝓓 where
  mdp := mdp
  verum := verum
  imply₁ := imply₁
  imply₂ := imply₂
  conj₁ := conj₁
  conj₂ := conj₂
  conj₃ := conj₃
  disj₁ := disj₁
  disj₂ := disj₂
  disj₃ := disj₃
  dne := dne

def maxm_subset
  (hRules : 𝓓₁.rules ≤ 𝓓₂.rules)
  (hAx : Ax(𝓓₁) ⊆ Ax(𝓓₂)) : (𝓓₁ ⊢ p) → (𝓓₂ ⊢ p)
  | maxm h => maxm (hAx h)
  | mdp ih₁ ih₂  => mdp (maxm_subset hRules hAx ih₁) (maxm_subset hRules hAx ih₂)
  | nec b h      => nec (by apply hRules.1; assumption) $ maxm_subset hRules hAx h
  | loeb b h     => loeb (by apply hRules.2.1; assumption) $ maxm_subset hRules hAx h
  | henkin b h   => henkin (by apply hRules.2.2; assumption) $ maxm_subset hRules hAx h
  | verum        => verum
  | imply₁ _ _   => imply₁ _ _
  | imply₂ _ _ _ => imply₂ _ _ _
  | conj₁ _ _    => conj₁ _ _
  | conj₂ _ _    => conj₂ _ _
  | conj₃ _ _    => conj₃ _ _
  | disj₁ _ _    => disj₁ _ _
  | disj₂ _ _    => disj₂ _ _
  | disj₃ _ _ _  => disj₃ _ _ _
  | dne _        => dne _

lemma maxm_subset! (hRules : 𝓓₁.rules ≤ 𝓓₂.rules) (hAx : Ax(𝓓₁) ⊆ Ax(𝓓₂)) (h : 𝓓₁ ⊢! p) : 𝓓₂ ⊢! p := ⟨maxm_subset hRules hAx h.some⟩

@[simp]
lemma reducible_of_subset (hNec : 𝓓₁.rules ≤ 𝓓₂.rules) (hAx : Ax(𝓓₁) ⊆ Ax(𝓓₂) := by intro; aesop) : 𝓓₁ ≤ₛ 𝓓₂ := by
  intro p hp;
  apply maxm_subset! hNec hAx hp;

instance [HasNec 𝓓] : System.Necessitation 𝓓 where
  nec := nec HasNec.has_nec

instance [HasLoebRule 𝓓] : System.LoebRule 𝓓 where
  loeb := loeb HasLoebRule.has_loeb

instance [HasHenkinRule 𝓓] : System.HenkinRule 𝓓 where
  henkin := henkin HasHenkinRule.has_henkin

instance [IncludeK 𝓓] : System.HasAxiomK 𝓓 where
  K _ _ := maxm $ Set.mem_of_subset_of_mem (IncludeK.include_K) (by simp);

instance [Normal 𝓓] : System.K 𝓓 where

noncomputable def inducition!
  {motive  : (p : Formula α) → 𝓓 ⊢! p → Sort*}
  (hMaxm   : ∀ {p}, (h : p ∈ Ax(𝓓)) → motive p ⟨maxm h⟩)
  (hMdp    : ∀ {p q}, {hpq : 𝓓 ⊢! p ⟶ q} → {hp : 𝓓 ⊢! p} → motive (p ⟶ q) hpq → motive p hp → motive q ⟨mdp hpq.some hp.some⟩)
  (hNec    : (hasNec : 𝓓.rules.nec) → ∀ {p}, {hp : 𝓓 ⊢! p} → motive p hp → motive (□p) ⟨(nec hasNec hp.some)⟩)
  (hLoeb   : (hasLoeb : 𝓓.rules.loeb) → ∀ {p}, {hp : 𝓓 ⊢! □p ⟶ p} → motive (□p ⟶ p) hp → motive p ⟨loeb hasLoeb hp.some⟩)
  (hHenkin : (hasHenkin : 𝓓.rules.henkin) → ∀ {p}, {hp : 𝓓 ⊢! □p ⟷ p} → motive (□p ⟷ p) hp → motive p ⟨henkin hasHenkin hp.some⟩)
  (hVerum  : motive ⊤ ⟨verum⟩)
  (hImply₁ : ∀ {p q}, motive (p ⟶ q ⟶ p) $ ⟨imply₁ p q⟩)
  (hImply₂ : ∀ {p q r}, motive ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) $ ⟨imply₂ p q r⟩)
  (hConj₁  : ∀ {p q}, motive (p ⋏ q ⟶ p) $ ⟨conj₁ p q⟩)
  (hConj₂  : ∀ {p q}, motive (p ⋏ q ⟶ q) $ ⟨conj₂ p q⟩)
  (hConj₃  : ∀ {p q}, motive (p ⟶ q ⟶ p ⋏ q) $ ⟨conj₃ p q⟩)
  (hDisj₁  : ∀ {p q}, motive (p ⟶ p ⋎ q) $ ⟨disj₁ p q⟩)
  (hDisj₂  : ∀ {p q}, motive (q ⟶ p ⋎ q) $ ⟨disj₂ p q⟩)
  (hDisj₃  : ∀ {p q r}, motive ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)) $ ⟨disj₃ p q r⟩)
  (hDne    : ∀ {p}, motive (~~p ⟶ p) $ ⟨dne p⟩)
  : ∀ {p}, (d : 𝓓 ⊢! p) → motive p d := by
  intro p d;
  induction d.some with
  | maxm h => exact hMaxm h
  | mdp hpq hp ihpq ihp => exact hMdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | nec has hp ihp => exact hNec has (ihp ⟨hp⟩)
  | loeb has hp ihp => exact hLoeb has (ihp ⟨hp⟩)
  | henkin has hp ihp => exact hHenkin has (ihp ⟨hp⟩)
  | _ => aesop

noncomputable def inducition_with_nec [HasNecOnly 𝓓]
  {motive  : (p : Formula α) → 𝓓 ⊢ p → Sort*}
  (hMaxm   : ∀ {p}, (h : p ∈ Ax(𝓓)) → motive p (maxm h))
  (hMdp    : ∀ {p q}, (hpq : 𝓓 ⊢ p ⟶ q) → (hp : 𝓓 ⊢ p) → motive (p ⟶ q) hpq → motive p hp → motive q (mdp hpq hp))
  (hNec    : ∀ {p}, (hp : 𝓓 ⊢ p) → motive p hp → motive (□p) (nec HasNec.has_nec hp))
  (hVerum  : motive ⊤ verum)
  (hImply₁ : ∀ {p q}, motive (p ⟶ q ⟶ p) $ imply₁ p q)
  (hImply₂ : ∀ {p q r}, motive ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) $ imply₂ p q r)
  (hConj₁  : ∀ {p q}, motive (p ⋏ q ⟶ p) $ conj₁ p q)
  (hConj₂  : ∀ {p q}, motive (p ⋏ q ⟶ q) $ conj₂ p q)
  (hConj₃  : ∀ {p q}, motive (p ⟶ q ⟶ p ⋏ q) $ conj₃ p q)
  (hDisj₁  : ∀ {p q}, motive (p ⟶ p ⋎ q) $ disj₁ p q)
  (hDisj₂  : ∀ {p q}, motive (q ⟶ p ⋎ q) $ disj₂ p q)
  (hDisj₃  : ∀ {p q r}, motive ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)) $ disj₃ p q r)
  (hDne    : ∀ {p}, motive (~~p ⟶ p) $ dne p)
  : ∀ {p}, (d : 𝓓 ⊢ p) → motive p d := by
  intro p d;
  induction d with
  | maxm h => exact hMaxm h
  | mdp hpq hp ihpq ihp => exact hMdp hpq hp ihpq ihp
  | nec _ hp ihp => exact hNec hp ihp
  | loeb => have : 𝓓.rules.loeb = false := HasNecOnly.not_has_loeb; simp_all;
  | henkin => have : 𝓓.rules.henkin = false := HasNecOnly.not_has_henkin; simp_all;
  | _ => aesop

noncomputable def inducition_with_nec! [HasNecOnly 𝓓]
  {motive  : (p : Formula α) → 𝓓 ⊢! p → Sort*}
  (hMaxm   : ∀ {p}, (h : p ∈ Ax(𝓓)) → motive p ⟨maxm h⟩)
  (hMdp    : ∀ {p q}, {hpq : 𝓓 ⊢! p ⟶ q} → {hp : 𝓓 ⊢! p} → motive (p ⟶ q) hpq → motive p hp → motive q (hpq ⨀ hp))
  (hNec    : ∀ {p}, {hp : 𝓓 ⊢! p} → motive p hp → motive (□p) ⟨(nec HasNec.has_nec hp.some)⟩)
  (hVerum  : motive ⊤ ⟨verum⟩)
  (hImply₁ : ∀ {p q}, motive (p ⟶ q ⟶ p) $ ⟨imply₁ p q⟩)
  (hImply₂ : ∀ {p q r}, motive ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) $ ⟨imply₂ p q r⟩)
  (hConj₁  : ∀ {p q}, motive (p ⋏ q ⟶ p) $ ⟨conj₁ p q⟩)
  (hConj₂  : ∀ {p q}, motive (p ⋏ q ⟶ q) $ ⟨conj₂ p q⟩)
  (hConj₃  : ∀ {p q}, motive (p ⟶ q ⟶ p ⋏ q) $ ⟨conj₃ p q⟩)
  (hDisj₁  : ∀ {p q}, motive (p ⟶ p ⋎ q) $ ⟨disj₁ p q⟩)
  (hDisj₂  : ∀ {p q}, motive (q ⟶ p ⋎ q) $ ⟨disj₂ p q⟩)
  (hDisj₃  : ∀ {p q r}, motive ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)) $ ⟨disj₃ p q r⟩)
  (hDne    : ∀ {p}, motive (~~p ⟶ p) $ ⟨dne p⟩)
  : ∀ {p}, (d : 𝓓 ⊢! p) → motive p d := by
  intro p d;
  induction d using Deduction.inducition! with
  | hMaxm h => exact hMaxm h
  | hMdp ihpq ihp => exact hMdp ihpq ihp
  | hNec _ ihp => exact hNec ihp
  | hLoeb => have : 𝓓.rules.loeb = false := HasNecOnly.not_has_loeb; simp_all;
  | hHenkin => have : 𝓓.rules.henkin = false := HasNecOnly.not_has_henkin; simp_all;
  | _ => aesop

/-
instance : System.K (𝐊 : AxiomSet α) := K_of_subset_K (by rfl)

instance : System.K (𝐊 ∪ Λ : AxiomSet α) := K_of_subset_K

instance S4_of_subset_S4 (hS4 : 𝐒𝟒 ⊆ Λ := by simp) : System.S4 (Λ : AxiomSet α) where
  K _ _   := Deduction.maxm $ Set.mem_of_subset_of_mem hS4 (by simp);
  T _     := Deduction.maxm $ Set.mem_of_subset_of_mem hS4 (by simp);
  Four _  := Deduction.maxm $ Set.mem_of_subset_of_mem hS4 (by simp);

instance : System.S4 (𝐒𝟒 : AxiomSet α) := S4_of_subset_S4 (by rfl)
-/

end Deduction


namespace DeductionParameter

open DeductionParameter

private abbrev NecOnly (Ax : AxiomSet α) : DeductionParameter α where
  axiomSet := Ax
  rules := ⟨true, false, false⟩

protected abbrev K : DeductionParameter α := NecOnly 𝗞
notation "𝐊" => DeductionParameter.K
instance : Normal (α := α) 𝐊 where


protected abbrev KT : DeductionParameter α := NecOnly (𝗞 ∪ 𝗧)
notation "𝐊𝐓" => DeductionParameter.KT
instance : Normal (α := α) 𝐊𝐓 where


protected abbrev KD : DeductionParameter α := NecOnly (𝗞 ∪ 𝗗)
notation "𝐊𝐃" => DeductionParameter.KD
instance : Normal (α := α) 𝐊𝐃 where


protected abbrev K4 : DeductionParameter α := NecOnly (𝗞 ∪ 𝟰)
notation "𝐊𝟒" => DeductionParameter.K4
instance : Normal (α := α) 𝐊𝟒 where
instance : System.K4 (𝐊𝟒 : DeductionParameter α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)


protected abbrev K5 : DeductionParameter α := NecOnly (𝗞 ∪ 𝟱)
notation "𝐊𝟓" => DeductionParameter.K5
instance : Normal (α := α) 𝐊𝟓 where


protected abbrev S4 : DeductionParameter α := NecOnly (𝗞 ∪ 𝗧 ∪ 𝟰)
notation "𝐒𝟒" => DeductionParameter.S4
instance : Normal (α := α) 𝐒𝟒 where
instance : System.S4 (𝐒𝟒 : DeductionParameter α) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)


protected abbrev S5 : DeductionParameter α := NecOnly (𝗞 ∪ 𝗧 ∪ 𝟱)
notation "𝐒𝟓" => DeductionParameter.S5
instance : Normal (α := α) 𝐒𝟓 where


protected abbrev KT4B : DeductionParameter α := NecOnly (𝗞 ∪ 𝗧 ∪ 𝟰 ∪ 𝗕)
notation "𝐊𝐓𝟒𝐁" => DeductionParameter.KT4B
instance : Normal (α := α) 𝐊𝐓𝟒𝐁 where


protected abbrev GL : DeductionParameter α := NecOnly (𝗞 ∪ 𝗟)
notation "𝐆𝐋" => DeductionParameter.GL
instance : Normal (α := α) 𝐆𝐋 where
instance : System.GL (𝐆𝐋 : DeductionParameter α) where
  L _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev S4Dot2 : DeductionParameter α := NecOnly (𝗞 ∪ 𝗧 ∪ 𝟰 ∪ .𝟮)
notation "𝐒𝟒.𝟐" => DeductionParameter.S4Dot2
instance : Normal (α := α) 𝐒𝟒.𝟐 where


protected abbrev S4Dot3 : DeductionParameter α := NecOnly (𝗞 ∪ 𝗧 ∪ 𝟰 ∪ .𝟯)
notation "𝐒𝟒.𝟑" => DeductionParameter.S4Dot3
instance : Normal (α := α) 𝐒𝟒.𝟑 where


protected abbrev S4Grz : DeductionParameter α := NecOnly (𝗞 ∪ 𝗧 ∪ 𝟰 ∪ 𝗚𝗿𝘇)
notation "𝐒𝟒𝐆𝐫𝐳" => DeductionParameter.S4Grz
instance : Normal (α := α) 𝐒𝟒𝐆𝐫𝐳 where


protected abbrev Triv : DeductionParameter α := NecOnly (𝗞 ∪ 𝗧 ∪ 𝗧𝗰)
notation "𝐓𝐫𝐢𝐯" => DeductionParameter.Triv
instance : Normal (α := α) 𝐓𝐫𝐢𝐯 where
instance : System.Triv (𝐓𝐫𝐢𝐯 : DeductionParameter α) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  Tc _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev Ver : DeductionParameter α := NecOnly (𝗞 ∪ 𝗩𝗲𝗿)
notation "𝐕𝐞𝐫" => DeductionParameter.Ver
instance : Normal (α := α) 𝐕𝐞𝐫 where
instance : System.Ver (𝐕𝐞𝐫 : DeductionParameter α) where
  Ver _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)


/-- Logic of Pure Necessitation -/
protected abbrev N : DeductionParameter α := NecOnly ∅
notation "𝐍" => DeductionParameter.N

protected abbrev K4H : DeductionParameter α := NecOnly (𝗞 ∪ 𝟰 ∪ 𝗛)
notation "𝐊𝟒𝐇" => DeductionParameter.K4H
instance : Normal (α := α) 𝐊𝟒𝐇 where
instance : System.K4H (𝐊𝟒𝐇 : DeductionParameter α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  H _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev K4Loeb : DeductionParameter α where
  axiomSet := 𝗞 ∪ 𝟰
  rules := ⟨true, true, false⟩
notation "𝐊𝟒(𝐋)" => DeductionParameter.K4Loeb
instance : IncludeK (α := α) 𝐊𝟒(𝐋) where
instance : HasNec (α := α) 𝐊𝟒(𝐋) where
instance : HasLoebRule (α := α) 𝐊𝟒(𝐋) where
instance : System.K4Loeb (𝐊𝟒(𝐋) : DeductionParameter α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev K4Henkin : DeductionParameter α where
  axiomSet := 𝗞 ∪ 𝟰
  rules := ⟨true, false, true⟩
notation "𝐊𝟒(𝐇)" => DeductionParameter.K4Henkin
instance : IncludeK (α := α) 𝐊𝟒(𝐇) where
instance : HasNec (α := α) 𝐊𝟒(𝐇) where
instance : HasHenkinRule (α := α) 𝐊𝟒(𝐇) where
instance : System.K4Henkin (𝐊𝟒(𝐇) : DeductionParameter α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

/-- Solovey's Truth Provability Logic, remark necessitation is *not* permitted. -/
protected abbrev GLS : DeductionParameter α where
  axiomSet := System.theory 𝐆𝐋 ∪ 𝗧
  rules := ⟨false, false, false⟩
notation "𝐆𝐋𝐒" => DeductionParameter.GLS
instance : System.HasAxiomK (𝐆𝐋𝐒 : DeductionParameter α) where
  K _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) $ by simp [System.theory, System.axiomK!];
instance : System.HasAxiomL (𝐆𝐋𝐒 : DeductionParameter α) where
  L _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) $ by simp [System.theory, System.axiomK!];
instance : System.HasAxiomT (𝐆𝐋𝐒 : DeductionParameter α) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

end DeductionParameter

open System

lemma normal_reducible
  {𝓓₁ 𝓓₂ : DeductionParameter α} [𝓓₁.Normal] [𝓓₂.Normal]
  (hMaxm : ∀ {p : Formula α}, p ∈ Ax(𝓓₁) → 𝓓₂ ⊢! p) : (𝓓₁ : DeductionParameter α) ≤ₛ 𝓓₂ := by
  apply System.reducible_iff.mpr;
  intro p h;
  induction h using Deduction.inducition_with_nec! with
  | hMaxm hp => exact hMaxm hp;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp
  | hNec ihp => exact Necessitation.nec! ihp
  | _ =>
    try first
    | apply verum!;
    | apply imply₁!;
    | apply imply₂!;
    | apply conj₁!;
    | apply conj₂!;
    | apply conj₃!;
    | apply disj₁!;
    | apply disj₂!;
    | apply disj₃!;
    | apply dne!;

lemma normal_reducible_subset {𝓓₁ 𝓓₂ : DeductionParameter α} [𝓓₁.Normal] [𝓓₂.Normal]
  (hSubset : Ax(𝓓₁) ⊆ Ax(𝓓₂)) : (𝓓₁ : DeductionParameter α) ≤ₛ 𝓓₂ := by
  apply normal_reducible;
  intro p hp;
  exact ⟨Deduction.maxm $ hSubset hp⟩;

lemma reducible_K_KT : (𝐊 : DeductionParameter α) ≤ₛ 𝐊𝐓 := by apply normal_reducible_subset; simp only [Set.subset_union_left];

lemma reducible_K_KD : (𝐊 : DeductionParameter α) ≤ₛ 𝐊𝐃 := by apply normal_reducible_subset; simp only [Set.subset_union_left];

lemma reducible_KT_S4 : (𝐊𝐓 : DeductionParameter α) ≤ₛ 𝐒𝟒 := by apply normal_reducible_subset; simp only [Set.subset_union_left];

lemma reducible_K4_S4 : (𝐊𝟒 : DeductionParameter α) ≤ₛ 𝐒𝟒 := by apply normal_reducible_subset; intro; aesop;

lemma reducible_S4_S4Dot2 : (𝐒𝟒 : DeductionParameter α) ≤ₛ 𝐒𝟒.𝟐 := by apply normal_reducible_subset; simp only [Set.subset_union_left];

lemma reducible_S4_S4Dot3 : (𝐒𝟒 : DeductionParameter α) ≤ₛ 𝐒𝟒.𝟑 := by apply normal_reducible_subset; simp only [Set.subset_union_left];

lemma reducible_S4_S4Grz : (𝐒𝟒 : DeductionParameter α) ≤ₛ 𝐒𝟒𝐆𝐫𝐳 := by apply normal_reducible_subset; simp only [Set.subset_union_left];

lemma reducible_K_GL : (𝐊 : DeductionParameter α) ≤ₛ 𝐆𝐋 := by apply normal_reducible_subset; simp only [Set.subset_union_left];

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
  induction h using Deduction.inducition! with
  | hMaxm hp =>
    rcases hp with (hK | hL)
    . obtain ⟨_, _, e⟩ := hK; subst_vars; exact axiomK!;
    . obtain ⟨_, e⟩ := hL; subst_vars; exact axiomL!;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hNec _ ihp => exact Necessitation.nec! ihp;
  | hLoeb _ ihp => exact LoebRule.loeb! ihp;
  | hHenkin => simp_all only [Bool.false_eq_true];
  | _ =>
    try first
    | apply verum!;
    | apply imply₁!;
    | apply imply₂!;
    | apply conj₁!;
    | apply conj₂!;
    | apply conj₃!;
    | apply disj₁!;
    | apply disj₂!;
    | apply disj₃!;
    | apply dne!;

lemma reducible_K4Loeb_K4Henkin : (𝐊𝟒(𝐋) : DeductionParameter α) ≤ₛ 𝐊𝟒(𝐇) := by
  apply System.reducible_iff.mpr;
  intro p h;
  induction h using Deduction.inducition! with
  | hMaxm hp =>
    rcases hp with (hK | hFour)
    . obtain ⟨_, _, e⟩ := hK; subst_vars; exact axiomK!;
    . obtain ⟨_, e⟩ := hFour; subst_vars; exact axiomFour!;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hNec _ ihp => exact Necessitation.nec! ihp;
  | hLoeb _ ihp => exact LoebRule.loeb! ihp;
  | hHenkin => simp_all only [Bool.false_eq_true];
  | _ =>
    try first
    | apply verum!;
    | apply imply₁!;
    | apply imply₂!;
    | apply conj₁!;
    | apply conj₂!;
    | apply conj₃!;
    | apply disj₁!;
    | apply disj₂!;
    | apply disj₃!;
    | apply dne!;

lemma reducible_K4Henkin_K4H : (𝐊𝟒(𝐇) : DeductionParameter α) ≤ₛ 𝐊𝟒𝐇 := by
  apply System.reducible_iff.mpr;
  intro p h;
  induction h using Deduction.inducition! with
  | hMaxm hp =>
    rcases hp with (hK | hFour)
    . obtain ⟨_, _, e⟩ := hK; subst_vars; exact axiomK!;
    . obtain ⟨_, e⟩ := hFour; subst_vars; exact axiomFour!;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hNec _ ihp => exact Necessitation.nec! ihp;
  | hHenkin _ ihp => exact HenkinRule.henkin! ihp;
  | hLoeb => simp_all only [Bool.false_eq_true];
  | _ =>
    try first
    | apply verum!;
    | apply imply₁!;
    | apply imply₂!;
    | apply conj₁!;
    | apply conj₂!;
    | apply conj₃!;
    | apply disj₁!;
    | apply disj₂!;
    | apply disj₃!;
    | apply dne!;

lemma reducible_K4Henkin_GL : (𝐊𝟒𝐇 : DeductionParameter α) ≤ₛ 𝐆𝐋 := by
  apply normal_reducible;
  intro p hp;
  rcases hp with (hK | hFour) | hH
  . obtain ⟨_, _, e⟩ := hK; subst_vars; exact axiomK!;
  . obtain ⟨_, _, e⟩ := hFour; subst_vars; exact axiomFour!;
  . obtain ⟨_, _, e⟩ := hH; subst_vars; exact axiomH!;

end GL

lemma reducible_GL_GLS : (𝐆𝐋 : DeductionParameter α) ≤ₛ 𝐆𝐋𝐒 := by
  apply System.reducible_iff.mpr;
  intro p h;
  exact ⟨Deduction.maxm (by left; exact h)⟩;

end LO.Modal.Standard
