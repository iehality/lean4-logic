import Logic.Propositional.Intuitionistic.Deduction
import Logic.Propositional.Intuitionistic.Kripke.Semantics

namespace LO.Propositional.Intuitionistic

open Formula Theory Kripke
open Hilbert
open Set


section Consistency

variable {Γ : Theory β} (hConsisΓ : Theory.Consistent Γ)

lemma consistent_subset_undeducible_falsum (hΔ : Δ ⊆ Γ) : (Δ ⊬ᴵ! ⊥) := Hilbert.consistent_subset_undeducible_falsum (· ⊢ᴵ ·) hConsisΓ hΔ

@[simp] lemma consistent_no_falsum : ⊥ ∉ Γ := Hilbert.consistent_no_falsum (· ⊢ᴵ ·) hConsisΓ
@[simp] lemma consistent_iff_undeducible_falsum : Consistent Γ ↔ (Γ ⊬ᴵ! ⊥) := Hilbert.consistent_iff_undeducible_falsum (· ⊢ᴵ ·) Γ
@[simp] lemma consistent_undeducible_falsum : Γ ⊬ᴵ! ⊥ := consistent_iff_undeducible_falsum.mp hConsisΓ

lemma consistent_neither_undeducible : (Γ ⊬ᴵ! p) ∨ (Γ ⊬ᴵ! ~p) := Hilbert.consistent_neither_undeducible (· ⊢ᴵ ·) hConsisΓ p

lemma consistent_of_undeducible : (Γ ⊬ᴵ! p) → Consistent Γ := by
  intros;
  simp [consistent_iff_undeducible_falsum];
  by_contra hC;
  have : Γ ⊢ᴵ! p := efq'! (by simpa [Undeducible] using hC);
  contradiction;

end Consistency


namespace Theory

def Closed (Γ : Theory β) := ∀ {p}, (Γ ⊢ᴵ! p) → (p ∈ Γ)

def Disjunctive (Γ : Theory β) := ∀ {p q}, (p ⋎ q ∈ Γ) → (p ∈ Γ) ∨ (q ∈ Γ)

class Prime (T : Theory β) where
  consistent : Consistent T
  closed : Closed T
  disjunctive : Disjunctive T

end Theory

structure PrimeTheory (β) where
  theory : Theory β
  prime : Prime theory

namespace PrimeTheory

@[simp] def membership (p : Formula β) (Ω : PrimeTheory β) := p ∈ Ω.theory
instance : Membership (Formula β) (PrimeTheory β) := ⟨membership⟩

@[simp] def subset (Ω₁ Ω₂ : PrimeTheory β) := Ω₁.theory ⊆ Ω₂.theory
instance : HasSubset (PrimeTheory β) := ⟨subset⟩

variable (Ω : PrimeTheory β)

def consistent : Consistent Ω.theory := Ω.prime.consistent

def closed : Closed Ω.theory := Ω.prime.closed

lemma closed' {p : Formula β} : (Ω.theory ⊢ᴵ! p) → (p ∈ Ω) := Ω.closed p

def disjunctive : Disjunctive Ω.theory := Ω.prime.disjunctive

lemma disjunctive' {p q : Formula β} : (p ⋎ q ∈ Ω) → (p ∈ Ω) ∨ (q ∈ Ω) := Ω.disjunctive p q

variable {Ω}

@[simp] lemma undeducible_falsum : Ω.theory ⊬ᴵ! ⊥ := consistent_undeducible_falsum Ω.consistent

@[simp] lemma no_falsum : ⊥ ∉ Ω := consistent_no_falsum Ω.consistent

end PrimeTheory

section

open Encodable
open Classical

variable {Γ : Theory β} {p : Formula β} (hD : Γ ⊬ᴵ! p)
variable [Encodable (Formula β)]

@[simp]
def insert_family (Γ : Theory β) (p : Formula β) : ℕ → Theory β
  | 0 => Γ
  | n + 1 =>
    match (decode n) with
    | some (q : Formula β) =>
      match q with
      | q₁ ⋎ q₂ =>
        if (insert_family Γ p n) ⊢ᴵ! (q₁ ⋎ q₂)
          then if (insert q₁ (insert_family Γ p n)) ⊢ᴵ! p
            then insert q₂ (insert_family Γ p n)
            else insert q₁ (insert_family Γ p n)
          else (insert_family Γ p n)
      | _ => insert_family Γ p n
    | _ => insert_family Γ p n
notation Γ "[" p "," i "]ᴵ" => insert_family Γ p i


lemma insert_family_mono (h : k ≤ m) : Γ[p, k]ᴵ ⊆ Γ[p, m]ᴵ := by
  induction h with
  | refl => rfl;
  | step h ih =>
    simp;
    split;
    . split;
      . split;
        . split;
          apply Set.Subset.trans ih; aesop;
          apply Set.Subset.trans ih; aesop;
        . simpa;
      . simpa;
    . simpa;

lemma insert_family_subset_self : Γ ⊆ Γ[p, k]ᴵ := insert_family_mono (zero_le k)

lemma insert_family_undeducible : ∀ {i}, Γ[p, i]ᴵ ⊬ᴵ! p := by
  intro i;
  induction i with
  | zero => simpa;
  | succ i ih =>
    simp;
    cases @decode (Formula β) _ i with
    | none => simpa;
    | some q =>
      simp;
      split;
      . split;
        . split;
          . rename_i q₁ q₂ hq₁₂ hq₁;
            by_contra hq₂;
            replace hq₁ : Γ[p,i]ᴵ ⊢ᴵ! (q₁ ⟶ p) := dtr! (by simpa [Undeducible] using hq₁);
            replace hq₂ : Γ[p,i]ᴵ ⊢ᴵ! (q₂ ⟶ p) := dtr! (by simpa [Undeducible] using hq₂);
            have : Γ[p,i]ᴵ ⊢ᴵ! p := disj₃'! hq₁ hq₂ hq₁₂;
            contradiction;
          . simpa;
        . simpa;
      . simpa;

lemma insert_family_deducible : (Γ[p, i]ᴵ ⊢ᴵ! p) → (Γ ⊢ᴵ! p) := by
  contrapose;
  intro h;
  exact insert_family_undeducible h

@[simp]
def prime_family (Γ : Theory β) (p : Formula β) : ℕ → Theory β
  | 0 => Γ
  | n + 1 => ⋃ i, (prime_family Γ p n)[p, i]ᴵ
notation Γ "[" p "," i "]ᴾ" => prime_family Γ p i

lemma prime_family_mono (h : k ≤ m) : Γ[p, k]ᴾ ⊆ Γ[p, m]ᴾ := by
  induction h with
  | refl => rfl;
  | @step m _ ih =>
    apply Subset.trans ih;
    nth_rw 1 [(show Γ[p, m]ᴾ = (Γ[p, m]ᴾ)[p, 0]ᴵ by rfl)];
    apply subset_iUnion;

lemma insert_family_deducible_of_prime_family_deducible (h : Γ[p, k + 1]ᴾ ⊢ᴵ! p) : ∃ m, (Γ[p, k]ᴾ[p, m]ᴵ ⊢ᴵ! p) := by
  sorry;

lemma prime_family_deducible : (Γ[p, k]ᴾ ⊢ᴵ! p) → (Γ ⊢ᴵ! p) := by
  induction k with
  | zero => simp;
  | succ k ih =>
    intro h;
    obtain ⟨m, hm⟩ := insert_family_deducible_of_prime_family_deducible h;
    exact ih (insert_family_deducible hm);

lemma prime_family_undeducible : Γ ⊬ᴵ! p → ∀ {k}, Γ[p, k]ᴾ ⊬ᴵ! p := by
  contrapose;
  intro h;
  obtain ⟨k, (hk : Γ[p, k]ᴾ ⊢ᴵ! p)⟩ := by simpa [Undeducible] using h;
  simpa [Undeducible] using prime_family_deducible hk;

@[simp]
def prime_family_union (Γ : Theory β) (p : Formula β) : Theory β := ⋃ i, Γ[p, i]ᴾ
notation Γ "[" p "]ᴾ" => prime_family_union Γ p

lemma mem_prime_family_union (h : q ∈ (Γ[p, m]ᴾ)[p, k]ᴵ) : q ∈ Γ[p]ᴾ := by
  simp;
  existsi (m + 1);
  simp;
  existsi k;
  simpa;

lemma prime_family_union_disjunctive : Disjunctive (Γ[p]ᴾ) := by
  intros q₁ q₂ hq;
  let k := encode (q₁ ⋎ q₂);
  obtain ⟨m, hm⟩ := by simpa using hq;
  have hm₀ : (Γ[p, m]ᴾ)[p, 0]ᴵ ⊢ᴵ! q₁ ⋎ q₂ := by simpa using axm! hm;
  have hmₖ : (Γ[p, m]ᴾ)[p, k]ᴵ ⊢ᴵ! q₁ ⋎ q₂ := weakening! (insert_family_mono (zero_le k)) hm₀;
  have h : q₁ ∈ (Γ[p, m]ᴾ)[p, k + 1]ᴵ ∨ q₂ ∈ (Γ[p, m]ᴾ)[p, k + 1]ᴵ := by
    simp [k, hmₖ];
    split;
    . right; simp;
    . left; simp;
  cases h with
  | inl h => left; apply mem_prime_family_union h;
  | inr h => right; apply mem_prime_family_union h;

lemma exists_prime_family_union_deducible : Γ[p]ᴾ ⊢ᴵ! q → ∃ k, Γ[p, k]ᴾ ⊢ᴵ! q := by
  sorry;

lemma prime_family_union_closed : Closed (Γ[p]ᴾ) := by
  intro q hq;
  let k := encode (p ⋎ q);
  have hpq : Γ[p]ᴾ ⊢ᴵ! (p ⋎ q) := disj₂'! hq;
  obtain ⟨m, hm⟩ := exists_prime_family_union_deducible hpq;
  have hm₀ : (Γ[p, m]ᴾ)[p, 0]ᴵ ⊢ᴵ! p ⋎ q := by simpa;
  have hmₖ : (Γ[p, m]ᴾ)[p, k]ᴵ ⊢ᴵ! p ⋎ q := weakening! (insert_family_mono (zero_le k)) hm₀;
  have h : q ∈ (Γ[p, m]ᴾ)[p, k + 1]ᴵ := by simp [k, hmₖ, axm!];
  exact mem_prime_family_union h;

lemma prime_family_union_undeducible : Γ[p]ᴾ ⊬ᴵ! p := by
  by_contra hC;
  replace hC : Γ[p]ᴾ ⊢ᴵ! p := by simpa [Undeducible] using hC;
  obtain ⟨m, (hm : Γ[p, m]ᴾ ⊢ᴵ! p)⟩ := exists_prime_family_union_deducible hC;
  have : Γ[p, m]ᴾ ⊬ᴵ! p := prime_family_undeducible hD;
  contradiction;

lemma prime_family_union_consistent : Theory.Consistent (Γ[p]ᴾ) := by
  by_contra hC;
  replace hC : Γ[p]ᴾ ⊢ᴵ! ⊥ := by simpa [Undeducible] using hC;
  have : Γ[p]ᴾ ⊬ᴵ! p := prime_family_union_undeducible hD;
  have : Γ[p]ᴾ ⊢ᴵ! p := efq'! hC;
  contradiction;

lemma prime_family_union_subset_self : Γ ⊆ Γ[p]ᴾ := by
  intro q hq;
  simp [prime_family_union];
  existsi 0;
  simpa;

lemma prime_expansion : ∃ Ω : PrimeTheory β, (Γ ⊆ Ω.theory ∧ Ω.theory ⊬ᴵ! p) := by
  let Ω : PrimeTheory β := ⟨Γ[p]ᴾ, ⟨prime_family_union_consistent hD, prime_family_union_closed, prime_family_union_disjunctive⟩⟩;
  existsi Ω;
  constructor;
  . apply prime_family_union_subset_self;
  . apply prime_family_union_undeducible hD;

end

variable [Encodable (Formula β)] -- TODO: remove

def CanonicalModel (β) : Kripke.Model (PrimeTheory β) β where
  frame Ω₁ Ω₂ := Ω₁ ⊆ Ω₂
  val Ω p := atom p ∈ Ω
  trans Ω₁ Ω₂ Ω₃ := Set.Subset.trans
  refl Ω := by simpa using Set.Subset.rfl;
  herditary h p hp := by apply h; exact hp;

@[simp]
lemma CanonicalModel.frame_def {Ω₁ Ω₂ : PrimeTheory β} : (CanonicalModel β).frame Ω₁ Ω₂ ↔ Ω₁ ⊆ Ω₂ := by rfl

@[simp]
lemma CanonicalModel.val_def {a : β} : (CanonicalModel β).val Ω a ↔ (atom a) ∈ Ω := by rfl

variable [DecidableEq β]

lemma truthlemma {Ω : PrimeTheory β} {p : Formula β} : (Ω ⊩[(CanonicalModel β)] p) ↔ (Ω.theory ⊢ᴵ! p) := by
  induction p using rec' generalizing Ω with
  | hatom a =>
    constructor;
    . intro h;
      exact ⟨Deduction.axm (CanonicalModel.val_def.mpr h)⟩;
    . apply PrimeTheory.closed;
  | hfalsum => simp; exact PrimeTheory.undeducible_falsum;
  | hand p q ihp ihq =>
    constructor;
    . intro h;
      obtain ⟨hp, hq⟩ := h;
      have dp : Ω.theory ⊢ᴵ! p := ihp.mp hp;
      have dq : Ω.theory ⊢ᴵ! q := ihq.mp hq;
      exact conj₃'! dp dq;
    . intro h;
      constructor;
      . apply ihp.mpr; exact conj₁'! h;
      . apply ihq.mpr; exact conj₂'! h;
  | hor p q ihp ihq =>
    constructor;
    . intro h; simp at h;
      cases h with
      | inl h => simp [ihp] at h; exact disj₁'! h;
      | inr h => simp [ihq] at h; exact disj₂'! h;
    . intro h;
      cases Ω.disjunctive' (Ω.closed' h) with
      | inl h => left; exact ihp.mpr ⟨.axm h⟩;
      | inr h => right; exact ihq.mpr ⟨.axm h⟩;
  | himp p q ihp ihq =>
    constructor;
    . contrapose;
      intro h;
      simp [KripkeSatisfies.imp_def'];
      have h₁ : insert p Ω.theory ⊬ᴵ! q := dtr_not! h;
      obtain ⟨Ω', hΩ'₁, hΩ'₂⟩ := prime_expansion h₁;
      existsi Ω';
      exact ⟨
        ihp.mpr $ axm! (by aesop),
        Set.Subset.trans
          (show Ω.theory ⊆ insert p Ω.theory by aesop)
          (show insert p Ω.theory ⊆ Ω'.theory by aesop),
        ihq.not.mpr hΩ'₂
      ⟩;
    . intro h;
      simp [KripkeSatisfies.imp_def'];
      by_contra hC; simp at hC;
      obtain ⟨Ω', ⟨hp, hΩΩ', hq⟩⟩ := hC;
      have hp : Ω'.theory ⊢ᴵ! p := ihp.mp hp;
      have hq : Ω'.theory ⊬ᴵ! q := ihq.not.mp hq;
      have := modus_ponens'! (weakening! hΩΩ' h) hp;
      contradiction;

lemma Kripke.completes {Γ : Theory β} {p : Formula β} : (Γ ⊨ᴵ p) → (Γ ⊢ᴵ! p) := by
  contrapose;
  intro hnp hp;
  have ⟨Ω, ⟨hsΩ, hnpΩ⟩⟩ := prime_expansion hnp;
  have := truthlemma.not.mpr hnpΩ;
  have := hp (CanonicalModel β) Ω (by
    intro q hq;
    exact truthlemma.mpr ⟨(Deduction.axm (hsΩ hq))⟩;
  );
  contradiction;

end LO.Propositional.Intuitionistic
