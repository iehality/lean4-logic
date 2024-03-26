import Logic.Logic.LogicSymbol

namespace LO

class Deduction {F : Type*} (Bew : Set F → F → Type*) where
  axm : ∀ {f}, f ∈ Γ → Bew Γ f
  weakening' : ∀ {T U f}, T ⊆ U → Bew T f → Bew U f

namespace Deduction

variable {F : Type*} [LogicalConnective F] (Bew : Set F → F → Type*) [Deduction Bew]

variable (Γ : Set F) (p : F)

def Deducible := Nonempty (Bew Γ p)

def Undeducible := ¬Deducible Bew Γ p

def Inconsistent := Deducible Bew Γ ⊥

def Consistent := Undeducible Bew Γ ⊥

variable {Bew Γ p}

lemma not_consistent : ¬Consistent Bew Γ ↔ Deducible Bew Γ ⊥ := by simp [Consistent, Undeducible]

lemma axm! (h : p ∈ Γ) : Deducible Bew Γ p := ⟨axm h⟩

end Deduction

namespace Hilbert

variable {F : Type*} [LogicalConnective F] [DecidableEq F] [NegDefinition F]

section

variable (Bew : Set F → F → Type*)

class HasModusPonens where
  modus_ponens {Γ₁ Γ₂ p q} : Bew Γ₁ (p ⟶ q) → Bew Γ₂ p → Bew (Γ₁ ∪ Γ₂) q

section

variable {Bew : Set F → F → Type*}

def HasModusPonens.of' [Deduction Bew] (b : {Γ : Set F} → {p q : F} → Bew Γ (p ⟶ q) → Bew Γ p → Bew Γ q) : HasModusPonens Bew :=
  ⟨fun {Γ₁ Γ₂ _ _}  b₁ b₂ ↦ b (Deduction.weakening' (Set.subset_union_left Γ₁ Γ₂) b₁) (Deduction.weakening' (Set.subset_union_right Γ₁ Γ₂) b₂)⟩

variable [HasModusPonens Bew]

abbrev modus_ponens {Γ₁ Γ₂ p q} (d₁ : Bew Γ₁ (p ⟶ q)) (d₂ : Bew Γ₂ p) : Bew (Γ₁ ∪ Γ₂) q := HasModusPonens.modus_ponens d₁ d₂
infixr:90 "⨀" => modus_ponens

def modus_ponens' {Γ p q} (d₁ : Bew Γ (p ⟶ q)) (d₂ : Bew Γ p) : Bew Γ q := by simpa using d₁ ⨀ d₂
infixr:90 "⨀" => modus_ponens'

end

/--
  Minimal Propositional Logic.
-/
class Minimal [NegDefinition F] extends Deduction Bew, HasModusPonens Bew where
  verum  (Γ : Set F)             : Bew Γ ⊤
  imply₁ (Γ : Set F) (p q : F)   : Bew Γ (p ⟶ (q ⟶ p))
  imply₂ (Γ : Set F) (p q r : F) : Bew Γ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
  conj₁  (Γ : Set F) (p q : F)   : Bew Γ (p ⋏ q ⟶ p)
  conj₂  (Γ : Set F) (p q : F)   : Bew Γ (p ⋏ q ⟶ q)
  conj₃  (Γ : Set F) (p q : F)   : Bew Γ (p ⟶ q ⟶ p ⋏ q)
  disj₁  (Γ : Set F) (p q : F)   : Bew Γ (p ⟶ p ⋎ q)
  disj₂  (Γ : Set F) (p q : F)   : Bew Γ (q ⟶ p ⋎ q)
  disj₃  (Γ : Set F) (p q r : F) : Bew Γ ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q) ⟶ r)

/-- Supplymental -/
class HasDT where
  dtr {Γ : Set F} {p q : F} : Bew (insert p Γ) q → Bew Γ (p ⟶ q)

class HasEFQ where
  efq (Γ : Set F) (p : F) : Bew Γ (⊥ ⟶ p)

class HasWeakLEM where
  wlem (Γ : Set F) (p : F) : Bew Γ (~p ⋎ ~~p)

class HasLEM where
  lem (Γ : Set F) (p : F) : Bew Γ (p ⋎ ~p)

class HasDNE where
  dne (Γ : Set F) (p : F) : Bew Γ (~~p ⟶ p)

class HasDummett where
  dummett (Γ : Set F) (p q : F) : Bew Γ ((p ⟶ q) ⋎ (q ⟶ p))

class HasPeirce where
  peirce (Γ : Set F) (p q : F) : Bew Γ (((p ⟶ q) ⟶ p) ⟶ p)

class Compact where
  compact {Γ p} : (Bew Γ p) → ((Δ : { Δ : Finset F | ↑Δ ⊆ Γ}) × (Bew ↑Δ p))

/--
  Intuitionistic Propositional Logic.

  Modal companion of `𝐒𝟒`
-/
class Intuitionistic extends Minimal Bew, HasEFQ Bew

/--
  Propositional Logic for Weak Law of Excluded Middle.

  Modal companion of `𝐒𝟒.𝟐`
-/
class WeakLEM extends Intuitionistic Bew, HasWeakLEM Bew


/--
  Gödel-Dummett Propositional Logic.

  Modal companion of `𝐒𝟒.𝟑`
-/
class GD extends Intuitionistic Bew, HasDummett Bew

/--
  Classical Propositional Logic.

  Modal companion of `𝐒𝟓`
-/
class Classical extends Minimal Bew, HasDNE Bew

end

open Deduction Minimal HasDT Intuitionistic Classical HasDNE

variable {Bew : Set F → F → Type*} (Γ : Set F) (p q r : F)

section Minimal

variable [hM : Minimal Bew] [hDT : HasDT Bew] [hEFQ : HasEFQ Bew]

abbrev efq := hEFQ.efq

def efq' {Γ p} : (Bew Γ ⊥) → (Bew Γ p) := modus_ponens' (efq _ _)

abbrev dtr {Γ p q} (d : Bew (insert p Γ) q) := HasDT.dtr d

def verum (Γ : Set F) : Bew Γ ⊤ := hM.verum Γ

abbrev imply₁ := hM.imply₁

def imply₁' {Γ p q} : Bew Γ p → Bew Γ (q ⟶ p) := modus_ponens' (imply₁ _ _ _)

abbrev imply₂ := hM.imply₂

def imply₂' {Γ p q r} (d₁ : Bew Γ (p ⟶ q ⟶ r)) (d₂ : Bew Γ (p ⟶ q)) (d₃ : Bew Γ p) : Bew Γ r := (((imply₂ _ _ _ _) ⨀ d₁) ⨀ d₂) ⨀ d₃

abbrev conj₁ := hM.conj₁

def conj₁' {Γ p q} : Bew Γ (p ⋏ q) → Bew Γ p := modus_ponens' (conj₁ _ _ _)

abbrev conj₂ := hM.conj₂

def conj₂' {Γ p q} : Bew Γ (p ⋏ q) → Bew Γ q := modus_ponens' (conj₂ _ _ _)

abbrev conj₃ := hM.conj₃

def conj₃' {Γ p q} (d₁ : Bew Γ p) (d₂: Bew Γ q) : Bew Γ (p ⋏ q) := (conj₃ _ _ _ ⨀ d₁) ⨀ d₂

abbrev disj₁ := hM.disj₁

def disj₁' {Γ p q} (d : Bew Γ p) : Bew Γ (p ⋎ q) := (disj₁ _ _ _ ⨀ d)

abbrev disj₂ := hM.disj₂

def disj₂' {Γ p q} (d : Bew Γ q) : Bew Γ (p ⋎ q) := (disj₂ _ _ _ ⨀ d)

abbrev disj₃ := hM.disj₃

def disj₃' {Γ p q r} (d₁ : Bew Γ (p ⟶ r)) (d₂ : Bew Γ (q ⟶ r)) (d₃ : Bew Γ (p ⋎ q)) : Bew Γ r := (((disj₃ _ _ _ _) ⨀ d₁) ⨀ d₂) ⨀ d₃

def disj_symm' {Γ p q} : Bew Γ (p ⋎ q) → Bew Γ (q ⋎ p) := by
  intro h;
  exact disj₃' (disj₂ _ _ _) (disj₁ _ _ _) h;

def iff_mp' {Γ p q} (d : Bew Γ (p ⟷ q)) : Bew Γ (p ⟶ q) := by
  simp [LogicalConnective.iff] at d;
  exact conj₁' d

def iff_right' {Γ p q} (dpq : Bew Γ (p ⟷ q)) (dp : Bew Γ p) : Bew Γ q := (iff_mp' dpq) ⨀ dp

def iff_mpr' {Γ p q} (d : Bew Γ (p ⟷ q)) : Bew Γ (q ⟶ p) := by
  simp [LogicalConnective.iff] at d;
  exact conj₂' d

def iff_left' {Γ p q} (dpq : Bew Γ (p ⟷ q)) (dq : Bew Γ q) : Bew Γ p := (iff_mpr' dpq) ⨀ dq

def iff_intro {Γ p q} (dpq : Bew Γ (p ⟶ q)) (dqp : Bew Γ (q ⟶ p)) : Bew Γ (p ⟷ q) := by
  simp [LogicalConnective.iff];
  exact conj₃' dpq dqp

def iff_symm' {Γ p q} (d : Bew Γ (p ⟷ q)) : Bew Γ (q ⟷ p) := iff_intro (iff_mpr' d) (iff_mp' d)

def dtl {Γ p q} (d : Bew Γ (p ⟶ q)) : Bew (insert p Γ) q := modus_ponens' (weakening' (by simp) d) (axm (by simp))

def imp_id : Bew Γ (p ⟶ p) := ((imply₂ Γ p (p ⟶ p) p) ⨀ (imply₁ _ _ _)) ⨀ (imply₁ _ _ _)

def id_insert (Γ p) : Bew (insert p Γ) p := axm (by simp)

def id_singleton (p) : Bew {p} p := by simpa using id_insert ∅ p

def dni : Bew Γ (p ⟶ ~~p) := by
  simp [NegDefinition.neg]
  have h₁ : Bew (insert (p ⟶ ⊥) (insert p Γ)) (p ⟶ ⊥) := axm (by simp);
  have h₂ : Bew (insert (p ⟶ ⊥) (insert p Γ)) p := axm (by simp);
  apply dtr;
  apply dtr;
  exact h₁ ⨀ h₂;

def dni' {Γ p} : Bew Γ p → Bew Γ (~~p) := modus_ponens' (dni _ _)

def contra₀' {Γ p q} : Bew Γ (p ⟶ q) → Bew Γ (~q ⟶ ~p) := by
  intro h;
  simp [NegDefinition.neg];
  apply dtr;
  apply dtr;
  have d₁ : Bew (insert p $ insert (q ⟶ ⊥) Γ) (q ⟶ ⊥) := axm (by simp);
  have d₂ : Bew (insert p $ insert (q ⟶ ⊥) Γ) p := axm (by simp);
  simpa using d₁ ⨀ h ⨀ d₂;

def neg_iff' {Γ p q} (d : Bew Γ (p ⟷ q)) : Bew Γ (~p ⟷ ~q) := by
  simp only [LogicalConnective.iff];
  apply conj₃';
  . apply contra₀';
    apply iff_mpr' d;
  . apply contra₀';
    apply iff_mp' d

def imp_trans' {Γ p q r} (h₁ : Bew Γ (p ⟶ q)) (h₂ : Bew Γ (q ⟶ r)) : Bew Γ (p ⟶ r) := by
  apply dtr;
  have : Bew (insert p Γ) p := axm (by simp);
  have : Bew (insert p Γ) q := modus_ponens' (weakening' (by simp) h₁) this;
  have : Bew (insert p Γ) r := modus_ponens' (weakening' (by simp) h₂) this;
  exact this

def assoc_left' {Γ p q r} (h : Bew Γ ((p ⋏ q) ⋏ r)) : Bew Γ (p ⋏ (q ⋏ r)) := by
  have dpq := conj₁' h;
  have dp := conj₁' dpq;
  have dq := conj₂' dpq;
  have dr := conj₂' h;
  exact conj₃' dp (conj₃' dq dr)

def assoc_left (Γ p q r) : Bew Γ ((p ⋏ q) ⋏ r ⟶ p ⋏ (q ⋏ r)) := by
  apply dtr;
  exact assoc_left' (axm (by simp))

def assoc_right' {Γ p q r} (h : Bew Γ (p ⋏ (q ⋏ r))) : Bew Γ ((p ⋏ q) ⋏ r) := by
  have dp := conj₁' h;
  have dqr := conj₂' h;
  have dq := conj₁' dqr;
  have dr := conj₂' dqr;
  exact conj₃' (conj₃' dp dq) dr

def assoc_right (Γ p q r) : Bew Γ (p ⋏ (q ⋏ r) ⟶ (p ⋏ q) ⋏ r) := by
  apply dtr;
  exact assoc_right' (axm (by simp))

def assoc (Γ p q r) : Bew Γ ((p ⋏ q) ⋏ r ⟷ p ⋏ (q ⋏ r)) := iff_intro (by apply assoc_left) (by apply assoc_right)

def conj_symm' {Γ p q} : Bew Γ (p ⋏ q) → Bew Γ (q ⋏ p) := by
  intro h;
  exact conj₃' (conj₂' h) (conj₁' h);

def conj_symm (Γ p q) : Bew Γ ((p ⋏ q) ⟶ (q ⋏ p)) := by
  apply dtr;
  exact conj_symm' (axm (by simp))

def conj_symm_iff (Γ p q) : Bew Γ ((p ⋏ q) ⟷ (q ⋏ p)) := iff_intro (by apply conj_symm) (by apply conj_symm)

def iff_id (Γ p) : Bew Γ (p ⟷ p) := iff_intro (by apply imp_id) (by apply imp_id)

def imp_top {Γ p} (d : Bew Γ (⊤ ⟶ p)) : Bew Γ p := d ⨀ (verum Γ)

def iff_left_top {Γ p} (d : Bew Γ (⊤ ⟷ p)) : Bew Γ p := imp_top (iff_mp' d)

def iff_right_top {Γ p} (d : Bew Γ (p ⟷ ⊤)) : Bew Γ p := imp_top (iff_mpr' d)

def tne : Bew Γ (~~(~p) ⟶ ~p) := by
  have : Bew Γ (p ⟶ ~~p) := dni Γ p;
  have : Bew Γ (~~(~p) ⟶ ~p) := contra₀' (by assumption)
  assumption

def tne' {Γ p} : Bew Γ (~~(~p)) → Bew Γ (~p) := modus_ponens' (tne _ _)

def imp_swap' {Γ p q r} (h : Bew Γ (p ⟶ q ⟶ r)) : Bew Γ (q ⟶ p ⟶ r) := by
  apply dtr;
  apply dtr;
  rw [(show insert p (insert q Γ) = insert q (insert p Γ) by aesop)];
  apply dtl;
  apply dtl;
  simpa;

def dn_distribute_imp_left : Bew Γ (~~(p ⟶ q) ⟶ (~~p ⟶ ~~q)) := by
  have : Bew {p ⟶ q} (~~p ⟶ ~~q) := contra₀' $ contra₀' $ axm (by simp);
  have : Bew ∅ ((p ⟶ q) ⟶ ~~p ⟶ ~~q) := dtr (by simpa);
  have : Bew ∅ (~~p ⟶ (p ⟶ q) ⟶  ~~q) := imp_swap' (by simpa);
  have : Bew {~~p} ((p ⟶ q) ⟶ (~~q)) := by simpa using dtl this;
  have : Bew {~~p} (~~(p ⟶ q) ⟶ ~~(~~q)) := contra₀' $ contra₀' $ (by assumption);
  have : Bew {~~p} (~~(p ⟶ q) ⟶ ~~q) := imp_trans' (by assumption) $ tne _ (~q);
  have : Bew ∅ (~~p ⟶ ~~(p ⟶ q) ⟶ ~~q) := dtr (by simpa);
  have : Bew ∅ (~~(p ⟶ q) ⟶ ~~p ⟶  ~~q) := imp_swap' (by simpa);
  exact weakening' (by simp) this

def dn_distribute_imp_left' {Γ p q} : Bew Γ (~~(p ⟶ q)) → Bew Γ (~~p ⟶ ~~q) := modus_ponens' (dn_distribute_imp_left _ _ _)

def efq_incldue {Γ p q} (h₁ : p ∈ Γ) (h₂ : ~p ∈ Γ) : Bew Γ q := by
  have d₁ : Bew Γ p := axm h₁;
  have d₂ : Bew Γ (~p) := axm h₂;
  have := modus_ponens' (by simpa using d₂) d₁;
  exact efq' this

def imp_intro_of_or (Γ p q) : Bew Γ ((~p ⋎ q) ⟶ (p ⟶ q)) := by
  have d₁ : Bew Γ (~p ⟶ (p ⟶ q)) := by
    apply dtr;
    apply dtr;
    exact efq_incldue (show p ∈ insert p (insert (~p) Γ) by simp) (by simp);
  have d₂ : Bew Γ (q ⟶ (p ⟶ q)) := by
    apply dtr;
    apply dtr;
    exact axm (show q ∈ insert p (insert q Γ) by simp);
  exact ((disj₃ _ _ _ _) ⨀ d₁) ⨀ d₂

def neg_or (Γ p q) : Bew Γ (~(p ⋎ q) ⟶ (~p ⋏ ~q)) := by
  have d₁ : Bew ∅ (~(p ⋎ q) ⟶ ~p) := contra₀' $ disj₁ _ _ _;
  have d₂ : Bew ∅ (~(p ⋎ q) ⟶ ~q) := contra₀' $ disj₂ _ _ _;
  have : Bew {~(p ⋎ q)} (~p) := by simpa using dtl d₁;
  have : Bew {~(p ⋎ q)} (~q) := by simpa using dtl d₂;
  have : Bew ∅ (~(p ⋎ q) ⟶ (~p ⋏ ~q)) := dtr $ conj₃' (by simpa using dtl d₁) (by simpa using dtl d₂);
  exact weakening' (by simp) this;

def intro_bot_of_and (Γ p) : Bew Γ (p ⋏ ~p ⟶ ⊥) := by
  apply dtr;
  have : Bew {p ⋏ ~p} (p ⋏ ~p) := axm (by simp);
  have : Bew {p ⋏ ~p} p := conj₁' (by assumption);
  have : Bew {p ⋏ ~p} (~p) := conj₂' (by assumption);
  have : Bew {p ⋏ ~p} (p ⟶ ⊥) := by simpa;
  have : Bew {p ⋏ ~p} ⊥ := modus_ponens' (by assumption) (conj₁' (by assumption));
  exact weakening' (by simp) this

def dn_distribute_imp_right : Bew Γ ((~~p ⟶ ~~q) ⟶ ~~(p ⟶ q)) := by
  have : Bew ∅ (~(p ⟶ q) ⟶ ~(~p ⋎ q)) := contra₀' $ imp_intro_of_or _ p q;
  have : Bew ∅ (~(~p ⋎ q) ⟶ (~~p ⋏ ~q)) := neg_or _ (~p) q
  have : Bew ∅ (~(p ⟶ q) ⟶ (~~p ⋏ ~q)) := imp_trans' (by assumption) (by assumption);

  let Γ' := (insert (~(p ⟶ q)) (insert (~~p ⟶ ~~q) Γ));

  have d₁ : Bew Γ' ((~q ⋏ ~~p)) := weakening' (show {~(p ⟶ q)} ⊆ Γ' by aesop) $ conj_symm' $ by simpa using dtl this;
  have d₂ : Bew Γ' ((~q ⋏ ~~q)) := by
    have dnq : Bew Γ' (~q) := conj₁' d₁;
    have dnnq : Bew Γ' (~~q) := (axm (by aesop)) ⨀ (conj₂' d₁);
    exact conj₃' dnq dnnq;
  have d₃ : Bew Γ' ((~q ⋏ ~~q) ⟶ ⊥) := intro_bot_of_and _ (~q);
  have : Bew (insert (~(p ⟶ q)) (insert (~~p ⟶ ~~q) Γ)) ⊥ := d₃ ⨀ d₂;

  nth_rw 5 [NegDefinition.neg];
  apply dtr;
  apply dtr;

  assumption;

def dn_distribute_imp_right' {Γ p q} : Bew Γ (~~p ⟶ ~~q) → Bew Γ (~~(p ⟶ q)) := modus_ponens' (dn_distribute_imp_right _ _ _)

end Minimal

section Classical

variable [c : Classical Bew] [HasDT Bew]

def dne : Bew Γ (~~p ⟶ p) := c.dne Γ p

def dne' {Γ p} : (Bew Γ (~~p)) → (Bew Γ p) := modus_ponens' (dne _ _)

def equiv_dn : Bew Γ (p ⟷ ~~p) := by
  simp only [LogicalConnective.iff];
  exact (conj₃ _ _ _ ⨀ (dni _ _)) ⨀ (dne _ _);

instance : HasEFQ Bew where
  efq Γ p := by
    have h₁ : Bew (insert ⊥ Γ) (⊥ ⟶ (p ⟶ ⊥) ⟶ ⊥) := imply₁ (insert ⊥ Γ) ⊥ (p ⟶ ⊥);
    have h₂ : Bew (insert ⊥ Γ) (((p ⟶ ⊥) ⟶ ⊥) ⟶ p) := by simpa using dne (insert ⊥ Γ) p;
    exact dtr $ h₂ ⨀ h₁ ⨀ (axm (by simp));

instance : Intuitionistic Bew where

instance : HasLEM Bew where
  lem Γ p := by sorry;

end Classical

section

variable [LogicalConnective F] [NegDefinition F]
variable (Bew : Set F → F → Type u) [hd : Deduction Bew] [HasModusPonens Bew] [HasDT Bew] [Minimal Bew] [Classical Bew]

local infix:20 " ⊢ " => Bew

variable (Γ : Set F) (p : F)

section Deducible

variable {Bew : Set F → F → Type u} [Deduction Bew]
variable [HasDT Bew] [HasModusPonens Bew] [Minimal Bew]

local infix:20 "⊢!" => Deducible Bew
local infix:20 "⊬!" => Undeducible Bew

lemma axm! {Γ : Set F} {f : F} (h : f ∈ Γ) : Γ ⊢! f := ⟨axm h⟩

lemma weakening! {Γ Δ : Set F} {p : F} (h : Γ ⊆ Δ) (d : Γ ⊢! p) : Δ ⊢! p := ⟨weakening' h d.some⟩

lemma modus_ponens! {Γ₁ Γ₂ : Set F} {p q : F} (d₁ : Γ₁ ⊢! (p ⟶ q)) (d₂ : Γ₂ ⊢! p) : Deducible Bew (Γ₁ ∪ Γ₂) q := ⟨d₁.some ⨀ d₂.some⟩
lemma modus_ponens'! {Γ : Set F} {p q : F} (d₁ : Γ ⊢! (p ⟶ q)) (d₂ : Γ ⊢! p) : Γ ⊢! q := by simpa using modus_ponens! d₁ d₂

lemma verum! (Γ : Set F) : Γ ⊢! ⊤ := ⟨verum Γ⟩

lemma imply₁! (Γ : Set F) (p q : F) : Γ ⊢! (p ⟶ q ⟶ p) := ⟨imply₁ Γ p q⟩
lemma imply₁'! {Γ : Set F} {p q : F} (d : Γ ⊢! p) : Γ ⊢! (q ⟶ p) := ⟨imply₁' d.some⟩

lemma imply₂! (Γ : Set F) (p q r : F) : Γ ⊢! ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) := ⟨imply₂ Γ p q r⟩
lemma imply₂'! {Γ : Set F} {p q r : F} (d₁ : Γ ⊢! (p ⟶ q ⟶ r)) (d₂ : Γ ⊢! (p ⟶ q)) (d₃ : Γ ⊢! p) : Γ ⊢! r := ⟨imply₂' d₁.some d₂.some d₃.some⟩

lemma conj₁! (Γ : Set F) (p q : F) : Γ ⊢! (p ⋏ q ⟶ p) := ⟨conj₁ Γ p q⟩
lemma conj₁'! {Γ : Set F} {p q : F} (d : Γ ⊢! (p ⋏ q)) : Γ ⊢! p := ⟨conj₁' d.some⟩

lemma conj₂! (Γ : Set F) (p q : F) : Γ ⊢! (p ⋏ q ⟶ q) := ⟨conj₂ Γ p q⟩
lemma conj₂'! {Γ : Set F} {p q : F} (d : Γ ⊢! (p ⋏ q)) : Γ ⊢! q := ⟨conj₂' d.some⟩

lemma conj₃! (Γ : Set F) (p q : F) : Γ ⊢! (p ⟶ q ⟶ p ⋏ q) := ⟨conj₃ Γ p q⟩
lemma conj₃'! {Γ : Set F} {p q : F} (d₁ : Γ ⊢! p) (d₂: Γ ⊢! q) : Γ ⊢! (p ⋏ q) := ⟨conj₃' d₁.some d₂.some⟩

lemma disj₁! (Γ : Set F) (p q : F) : Γ ⊢! (p ⟶ p ⋎ q) := ⟨disj₁ Γ p q⟩
lemma disj₁'! {Γ : Set F} {p q : F} (d : Γ ⊢! p) : Γ ⊢! (p ⋎ q) := ⟨disj₁' d.some⟩

lemma disj₂! (Γ : Set F) (p q : F) : Γ ⊢! (q ⟶ p ⋎ q) := ⟨disj₂ Γ p q⟩
lemma disj₂'! {Γ : Set F} {p q : F} (d : Γ ⊢! q) : Γ ⊢! (p ⋎ q) := ⟨disj₂' d.some⟩

lemma disj₃! (Γ : Set F) (p q r : F) : Γ ⊢! ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q) ⟶ r) := ⟨disj₃ Γ p q r⟩
lemma disj₃'! {Γ : Set F} {p q r : F} (d₁ : Γ ⊢! (p ⟶ r)) (d₂ : Γ ⊢! (q ⟶ r)) (d₃ : Γ ⊢! (p ⋎ q)) : Γ ⊢! r := ⟨disj₃' d₁.some d₂.some d₃.some⟩

lemma disj_symm'! {Γ : Set F} {p q : F} (d : Γ ⊢! (p ⋎ q)) : Γ ⊢! (q ⋎ p) := ⟨disj_symm' d.some⟩

lemma efq! [HasEFQ Bew] (Γ : Set F) (p : F) : Γ ⊢! (⊥ ⟶ p) := ⟨efq Γ p⟩
lemma efq'! [HasEFQ Bew] {Γ : Set F} {p} (d : Γ ⊢! ⊥) : Γ ⊢! p := ⟨efq' d.some⟩

lemma dni! (Γ : Set F) (p : F) : Γ ⊢! (p ⟶ ~~p) := ⟨dni Γ p⟩
lemma dni'! {Γ : Set F} {p} (d : Γ ⊢! p) : Γ ⊢! (~~p) := ⟨dni' d.some⟩

lemma iff_intro! {Γ : Set F} {p q : F} (dpq : Γ ⊢! (p ⟶ q)) (dqp : Γ ⊢! (q ⟶ p)) : Γ ⊢! (p ⟷ q) := ⟨iff_intro dpq.some dqp.some⟩

lemma iff_symm'! {Γ : Set F} {p q : F} (d : Γ ⊢! (p ⟷ q)) : Γ ⊢! (q ⟷ p) := ⟨iff_symm' d.some⟩

lemma iff_mp'! {Γ : Set F} {p q : F} (d : Γ ⊢! (p ⟷ q)) : Γ ⊢! (p ⟶ q) := ⟨iff_mp' d.some⟩
lemma iff_mpr'! {Γ : Set F} {p q : F} (d : Γ ⊢! (p ⟷ q)) : Γ ⊢! (q ⟶ p) := ⟨iff_mpr' d.some⟩

lemma iff_left'! {Γ : Set F} {p q : F} (dpq : Γ ⊢! (p ⟷ q)) (dq : Γ ⊢! q) : Γ ⊢! p := ⟨iff_left' dpq.some dq.some⟩
lemma iff_right'! {Γ : Set F} {p q : F} (dpq : Γ ⊢! (p ⟷ q)) (dp : Γ ⊢! p) : Γ ⊢! q := ⟨iff_right' dpq.some dp.some⟩

lemma iff_def! {Γ : Set F} {p q : F} : (Γ ⊢! (p ⟷ q)) ↔ (Γ ⊢! (p ⟶ q)) ∧ (Γ ⊢! (q ⟶ p)) := by
  constructor;
  . intro h; exact ⟨iff_mp'! h, iff_mpr'! h⟩
  . intro h; exact iff_intro! h.1 h.2

lemma neg_iff'! {Γ : Set F} {p q : F} (d : Γ ⊢! (p ⟷ q)) : Γ ⊢! (~p ⟷ ~q) := ⟨neg_iff' d.some⟩

lemma contra₀'! {Γ : Set F} {p q : F} (d : Γ ⊢! (p ⟶ q)) : Γ ⊢! (~q ⟶ ~p) := ⟨contra₀' d.some⟩

lemma dtr! {Γ : Set F} {p q : F} (d : (insert p Γ) ⊢! q) : Γ ⊢! (p ⟶ q) := ⟨dtr d.some⟩
lemma dtr_not! {Γ : Set F} {p q : F} : (Γ ⊬! (p ⟶ q)) → ((insert p Γ) ⊬! q) := by
  contrapose;
  simp [Undeducible, Deducible];
  intro d;
  exact ⟨dtr d⟩

lemma dtl! {Γ : Set F} {p q : F} (d : Γ ⊢! (p ⟶ q)) : (insert p Γ) ⊢! q := ⟨dtl d.some⟩
lemma dtl_not! {Γ : Set F} {p q : F} : ((insert p Γ) ⊬! q) → (Γ ⊬! (p ⟶ q)) := by
  contrapose;
  simp [Undeducible, Deducible];
  intro d;
  exact ⟨dtl d⟩

lemma imp_id! (Γ : Set F) (p : F) : Γ ⊢! (p ⟶ p) := ⟨imp_id Γ p⟩

lemma imp_top! {Γ : Set F} {p : F} (d : Γ ⊢! (⊤ ⟶ p)) : Γ ⊢! p := ⟨imp_top d.some⟩

lemma iff_left_top! {Γ : Set F} {p : F} (d : Γ ⊢! (⊤ ⟷ p)) : Γ ⊢! p := ⟨iff_left_top d.some⟩
lemma iff_right_top! {Γ : Set F} {p : F} (d : Γ ⊢! (p ⟷ ⊤)) : Γ ⊢! p := ⟨iff_right_top d.some⟩

lemma imp_trans'! {Γ : Set F} {p q r : F} (h₁ : Γ ⊢! (p ⟶ q)) (h₂ : Γ ⊢! (q ⟶ r)) : Γ ⊢! (p ⟶ r) := ⟨imp_trans' h₁.some h₂.some⟩

lemma tne! (Γ : Set F) (p : F) : Γ ⊢! (~~(~p) ⟶ ~p) := ⟨tne Γ p⟩
lemma tne'! {Γ : Set F} {p} (d : Γ ⊢! (~~(~p))) : Γ ⊢! (~p) := ⟨tne' d.some⟩

section Intuitionistic

variable [Intuitionistic Bew]

lemma dn_distribute_imp_left! (Γ : Set F) (p q : F) : Γ ⊢! (~~(p ⟶ q) ⟶ (~~p ⟶ ~~q)) := ⟨dn_distribute_imp_left Γ p q⟩
lemma dn_distribute_imp_left'! {Γ : Set F} {p q : F} (d : Γ ⊢! (~~(p ⟶ q))) : Γ ⊢! (~~p ⟶ ~~q) := ⟨dn_distribute_imp_left' d.some⟩

lemma dn_disctribute_imp_right! (Γ : Set F) (p q : F) : Γ ⊢! ((~~p ⟶ ~~q) ⟶ ~~(p ⟶ q)) := ⟨dn_distribute_imp_right Γ p q⟩
lemma dn_disctribute_imp_right'! {Γ : Set F} {p q : F} (d : Γ ⊢! (~~p ⟶ ~~q)) : Γ ⊢! (~~(p ⟶ q)) := ⟨dn_distribute_imp_right' d.some⟩

end Intuitionistic

section Classical

variable [Classical Bew]

lemma dne! [HasDNE Bew] (Γ : Set F) (p : F) : Γ ⊢! (~~p ⟶ p) := ⟨dne Γ p⟩
lemma dne'! [HasDNE Bew] {Γ : Set F} {p} (d : Γ ⊢! (~~p)) : Γ ⊢! p := ⟨dne' d.some⟩

lemma equiv_dn! (Γ : Set F) (p : F) : Γ ⊢! (p ⟷ ~~p) := ⟨equiv_dn Γ p⟩

end Classical

end Deducible

section Consistency

local infix:20 "⊢!" => Deducible Bew
local infix:20 "⊬!" => Undeducible Bew

lemma consistent_iff_undeducible_falsum : Consistent Bew Γ ↔ (Γ ⊬! ⊥) := Iff.rfl

lemma consistent_no_falsum {Γ} (h : Consistent Bew Γ) : ⊥ ∉ Γ := fun hC ↦ h ⟨hd.axm hC⟩

lemma consistent_of_subset {Γ Δ : Set F} (h : Γ ⊆ Δ) (hConsis : Consistent Bew Δ) : Consistent Bew Γ :=
  fun hD ↦ hConsis ⟨hd.weakening' h hD.some⟩

lemma consistent_of_insert {p} (hConsis : Consistent Bew (insert p Γ)) : Consistent Bew Γ := consistent_of_subset Bew (by simp) hConsis

lemma consistent_no_falsum_subset {Γ Δ} (hConsis : Consistent Bew Γ) (hΔ : Δ ⊆ Γ) : ⊥ ∉ Δ := consistent_no_falsum Bew $ consistent_of_subset Bew hΔ hConsis

lemma consistent_subset_undeducible_falsum {Γ Δ} (hConsis : Consistent Bew Γ) (hΔ : Δ ⊆ Γ) : (Δ ⊬! ⊥) := by
  by_contra hC;
  simp_all [Consistent, Undeducible, Deducible];
  exact hConsis.false $ hd.weakening' hΔ hC.some;

lemma consistent_neither_undeducible {Γ : Set F} (hConsis : Consistent Bew Γ) (p) : (Γ ⊬! p) ∨ (Γ ⊬! ~p) := by
  by_contra hC; simp only [Undeducible, not_or] at hC;
  have h₁ : Γ ⊢! p  := by simpa using hC.1;
  have h₂ : Γ ⊢! p ⟶ ⊥ := by simpa using hC.2;
  exact hConsis $ modus_ponens'! h₂ h₁;

lemma inconsistent_of_deduction {Γ : Set F} (d : Γ ⊢ ⊥) : Inconsistent Bew Γ := ⟨d⟩

lemma inconsistent_of_deducible {Γ : Set F} (d : Γ ⊢! ⊥) : Inconsistent Bew Γ := by simpa [Inconsistent];

lemma inconsistent_insert_falsum : Inconsistent Bew (insert ⊥ Γ) := ⟨hd.axm (by simp)⟩

lemma inconsistent_insert {Γ p} (h : Inconsistent Bew (insert p Γ)) : (∃ Δ, (Δ ⊆ Γ) ∧ ((insert p Δ) ⊢! ⊥)) := by
  existsi Γ;
  constructor;
  . rfl;
  . exact h;

/--
  **This lemma require classical logic.**
-/
lemma inconsistent_iff_insert_neg {Γ p} : Inconsistent Bew (insert (~p) Γ) ↔ (Γ ⊢! p) := by
  constructor;
  . intro h;
    have : Γ ⊢ ~~p := by simpa using (dtr h.some);
    exact ⟨(dne' this)⟩
  . intro h;
    have : Γ ⊢ ((p ⟶ ⊥) ⟶ ⊥) := by simpa using dni' h.some
    exact ⟨by simpa using (dtl this)⟩;

lemma consistent_iff_insert_neg {Γ p} : Consistent Bew (insert (~p) Γ) ↔ (Γ ⊬! p) := (inconsistent_iff_insert_neg Bew).not

lemma consistent_either {Γ : Set F} (hConsis : Consistent Bew Γ) (p) : (Consistent Bew (insert p Γ)) ∨ (Consistent Bew (insert (~p) Γ)) := by
  by_contra hC; simp [Undeducible, not_or, Consistent] at hC;
  have ⟨Δ₁, hΔ₁, ⟨dΔ₁⟩⟩ := inconsistent_insert Bew hC.1;
  have ⟨Δ₂, hΔ₂, ⟨dΔ₂⟩⟩ := inconsistent_insert Bew hC.2;
  exact consistent_subset_undeducible_falsum _ hConsis (by aesop) ⟨(dtr dΔ₂) ⨀ (dtr dΔ₁)⟩;

end Consistency

end

end Hilbert

end LO
