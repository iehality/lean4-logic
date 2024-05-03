import Logic.Logic.LogicSymbol

open Function

namespace LO

class UnaryModalOperator (ι : Type*) (F : Type*) where
  mop (i : ι) : F → F
  mop_injective {i} : Function.Injective (mop i)

attribute [simp] UnaryModalOperator.mop_injective

namespace UnaryModalOperator

variable [UnaryModalOperator ι F]
variable {i : ι} {p q : F}

@[simp] lemma mop_injective' : ((mop i) p) = ((mop i) q) ↔ p = q := by constructor; intro h; exact mop_injective h; simp_all;

@[simp] def multimop (i : ι) (n : ℕ) (p : F) : F := Nat.iterate (mop i) n p

@[simp] lemma multimop_zero : (mop i)^[0] p = p := rfl

@[simp] lemma mzero : multimop i 0 = (id : F → F) := rfl

lemma multimop_succ : (mop i)^[(n + 1)] p = (mop i)^[n] ((mop i) p) := by apply iterate_succ_apply

@[simp] lemma multimop_succ' : (mop i)^[(n + 1)] p = (mop i) ((mop i)^[n] p) := by apply iterate_succ_apply'

lemma multimop_prepost : ((mop i) ((mop i)^[n] p)) = ((mop i)^[n] ((mop i) p)) := by induction n <;> simp_all

@[simp] lemma multimop_injective' : ((mop i)^[n] p = (mop i)^[n] q) ↔ (p = q) := by induction n <;> simp [*]

@[simp] lemma multimop_injective : Function.Injective (((mop i)^[n]) : F → F) := by apply Function.Injective.iterate (by simp);

end UnaryModalOperator

end LO


section

open LO UnaryModalOperator

variable [UnaryModalOperator ι F] [DecidableEq F]
variable {i : ι} {n : ℕ} {a : F}

namespace Set

variable {s t : Set F}

protected def multimop (i : ι) (n : ℕ) (s : Set F) : Set F := (multimop i n) '' s
notation:76 "△[" i:90 "]" "[" n:90 "]" s:max => Set.multimop i n s

@[simp] lemma multimop_empty : △[i][n](∅ : Set F) = ∅ := by simp [Set.multimop]

@[simp] lemma multimop_singleton : △[i][n]({a} : Set F) = {(mop i)^[n] a} := by simp [Set.multimop]

@[simp] lemma multimop_zero : △[i][0]s = s := by simp [Set.multimop]

@[simp] lemma multimop_mem_intro : a ∈ s → (mop i)^[n] a ∈ (△[i][n]s) := by tauto;

@[simp] lemma multimop_injOn : Set.InjOn (multimop i n) (multimop i n ⁻¹' s) := by simp [Set.InjOn];

@[simp] lemma multimop_subset (h : s ⊆ t) : (△[i][n]s) ⊆ (△[i][n]t) := by simp_all [Set.subset_def, Set.multimop];

@[simp] lemma multimop_union : (△[i][n](s ∪ t)) = (△[i][n]s) ∪ (△[i][n]t) := by simp_all [Set.image_union, Set.multimop];

lemma multimop_mem_iff : a ∈ (△[i][n]s) ↔ (∃ b ∈ s, (mop i)^[n] b = a) := by simp_all [Set.mem_image, Set.multimop];

lemma forall_multimop_of_subset_multimop (h : s ⊆ △[i][n]t) : ∀ p ∈ s, ∃ q ∈ t, p = (mop i)^[n] q := by
  intro p hp;
  obtain ⟨q, hq₁, hq₂⟩ := h hp;
  use q;
  simp_all;

protected def mop (i : ι) (s : Set F) : Set F := Set.multimop i 1 s
notation:76 "△[" i "]" s => Set.mop i s

@[simp] lemma mop_empty : (△[i](∅ : Set F)) = ∅ := by simp [Set.mop]

@[simp] lemma mop_singleton : (△[i]({a} : Set F)) = {(mop i a)} := by simp [Set.mop]

@[simp] lemma mop_mem_intro : a ∈ s → (mop i a) ∈ (△[i]s) := by apply multimop_mem_intro;

@[simp] lemma mop_injOn : Set.InjOn (multimop i n) s := by simp [Set.InjOn]

lemma mop_subset (h : s ⊆ t) : (△[i]s) ⊆ (△[i]t) := by apply multimop_subset; assumption;

@[simp] lemma mop_union : (△[i](s ∪ t)) = (△[i]s) ∪ (△[i]t) := by apply multimop_union;

lemma mop_mem_iff : p ∈ (△[i]s) ↔ (∃ q ∈ s, (mop i q) = p) := by apply multimop_mem_iff;

protected lemma mop_injective : Function.Injective (λ {s : Set F} => Set.mop i s) := Function.Injective.image_injective mop_injective

lemma forall_mop_of_subset_mop (h : s ⊆ (Set.mop i t)) : ∀ p ∈ s, ∃ q ∈ t, p = mop i q := forall_multimop_of_subset_multimop h


@[simp] protected def premultimop (i : ι) (n : ℕ) (s : Set F) := (multimop i n) ⁻¹' s
notation:76 "△⁻¹[" i:90 "]" "[" n:90 "]" s:max => Set.premultimop i n s

lemma multimop_premultimop_eq : △⁻¹[i][n](△[i][n]s) = s := by
  apply Set.preimage_image_eq;
  exact multimop_injective;

lemma premultimop_multimop_eq_of_subset_premultimop (hs : s ⊆ △[i][n]t) : △[i][n](△⁻¹[i][n]s) = s := by
  apply Set.eq_of_subset_of_subset;
  . intro p hp;
    obtain ⟨q, hq₁, hq₂⟩ := hp;
    simp_all [Set.premultimop];
  . intro p hp;
    obtain ⟨q, _, hq₂⟩ := forall_multimop_of_subset_multimop hs p hp;
    simp_all [multimop, Set.premultimop];


@[simp] lemma premultimop_multimop_subset : △[i][n](△⁻¹[i][n]s) ⊆ s := by simp [Set.subset_def, Set.multimop, Set.premultimop];

lemma premultimop_subset (h : s ⊆ t) : (△⁻¹[i][n]s) ⊆ (△⁻¹[i][n]t) := by simp_all [Set.subset_def, Set.premultimop];

lemma subset_premulitimop_iff_multimop_subset (h : s ⊆ △⁻¹[i][n]t) : △[i][n]s ⊆ t := by
  intro p hp;
  obtain ⟨_, h₁, h₂⟩ := multimop_subset h hp;
  subst h₂;
  assumption;

lemma subset_multimop_iff_premulitimop_subset (h : s ⊆ (△[i][n]t)) : (△⁻¹[i][n]s) ⊆ t := by
  intro p hp;
  obtain ⟨_, h₁, h₂⟩ := premultimop_subset h hp;
  simp_all;


protected def premop (i : ι) (s : Set F) := Set.premultimop i 1 s
notation:76 "△⁻¹[" i "]" s => Set.premop i s

@[simp] lemma mop_premop_eq : (△⁻¹[i]△[i]s) = s := by apply multimop_premultimop_eq;

lemma premop_mop_eq_of_subset_mop (hs : s ⊆ △[i]t) : (△[i]△⁻¹[i]s) = s := premultimop_multimop_eq_of_subset_premultimop hs

@[simp] lemma premop_mop_subset : (△[i]△⁻¹[i]s) ⊆ s := by apply premultimop_multimop_subset;

lemma premop_subset (h : s ⊆ t) : (△⁻¹[i]s) ⊆ (△⁻¹[i]t) := premultimop_subset h

lemma subset_premop_iff_mop_subset (h : s ⊆ △⁻¹[i]t) : (△[i]s) ⊆ t := subset_premulitimop_iff_multimop_subset h

lemma subset_mop_iff_premop_subset (h : s ⊆ △[i]t) : (△⁻¹[i]s) ⊆ t := subset_multimop_iff_premulitimop_subset h

end Set


namespace List

open LO
open UnaryModalOperator

variable {l : List F}

protected abbrev multimop (i : ι) (n : ℕ) (l : List F) : List F := l.map (multimop i n)
notation "△[" i:90 "]" "[" n:90 "]" l:max => List.multimop i n l

@[simp] protected def mop (i : ι) (l : List F) : List F := △[i][1]l
notation "△[" n:90 "]" l:max => List.mop n l

@[simp] lemma multimop_empty : △[i][n]([] : List F) = [] := by simp [List.multimop]

@[simp] protected lemma multimop_zero : △[i][0]l = l := by simp [List.multimop, multimop, multimop_zero]

def premultimop (i : ι) (n : ℕ) (l : List F) := l.filter (λ (p : F) => (mop i)^[n] p ∈ l)
notation "△⁻¹[" i:90 "]" "[" n:90 "]" l:max => List.premultimop i n l

@[simp] def premop (i : ι) (l : List F) := △[i][1]l
notation "△⁻¹[" i:90 "]" l:max => List.premop i l

end List


namespace Finset

variable {s t : Finset F}

@[simp] protected noncomputable def multimop (i : ι) (n : ℕ) (s : Finset F) : Finset F := (△[i][n](s.toList)).toFinset
notation "△[" i:90 "]" "[" n:90 "]" s:max => Finset.multimop i n s

@[simp] protected noncomputable def mop (i : ι) (s : Finset F) : Finset F := △[i][1]s
notation "△[" i:90 "]" s:max => Finset.mop i s

lemma multimop_def : (△[i][n]s : Finset F) = s.image (multimop i n) := by simp [List.multimop, List.toFinset_map];

lemma multimop_coe : ↑(△[i][n]s : Finset F) = △[i][n](↑s : Set F) := by simp_all [Set.multimop, List.multimop]; rfl;

@[simp] lemma multimop_zero : (△[i][0]s : Finset F) = s := by simp

@[simp]
lemma multimop_union : (△[i][n](s ∪ t) : Finset F) = (△[i][n]s ∪ △[i][n]t : Finset F) := by
  simp [List.toFinset_map, List.multimop];
  aesop;

lemma multimop_mem_coe {s : Finset F} : a ∈ Finset.multimop i n s ↔ a ∈ Set.multimop i n (↑s : Set F) := by
  constructor <;> simp_all [Set.multimop];

@[simp] noncomputable def premultimop (i : ι) (n : ℕ) (s : Finset F) : Finset F := s.preimage (multimop i n) (by simp)
notation "△⁻¹[" i:90 "]" "[" n:90 "]" s:max => Finset.premultimop i n s

@[simp] noncomputable def premop (i : ι) (s : Finset F) : Finset F := △⁻¹[i][1]s
notation "△⁻¹[" i:90 "]" s:max => Finset.premop i s

lemma premultimop_coe : ↑(△⁻¹[i][n]s : Finset F) = △⁻¹[i][n](↑s : Set F) := by apply Finset.coe_preimage;

lemma premop_coe : ↑(△⁻¹[i]s : Finset F) = △⁻¹[i](↑s : Set F) := by apply premultimop_coe;

lemma premultimop_multimop_eq_of_subset_multimop {s : Finset F} {t : Set F} (hs : ↑s ⊆ △[i][n]t) : (△[i][n](△⁻¹[i][n]s : Finset F) : Finset F) = s := by
  have := Set.premultimop_multimop_eq_of_subset_premultimop hs;
  rw [←premultimop_coe, ←multimop_coe] at this;
  exact Finset.coe_inj.mp this;

end Finset

end


namespace LO

open UnaryModalOperator

/--
  Standard modal logic, which has 2 modal unary operators `□`, `◇`, and `◇` is defined as dual of `□`
-/
class StandardModalLogicalConnective (F : Sort _) extends LogicalConnective F, UnaryModalOperator Bool F where
  duality {p : F} : (mop false) p = ~((mop true) (~p))

namespace StandardModalLogicalConnective

variable [StandardModalLogicalConnective F] [DecidableEq F]

@[match_pattern]
abbrev box : F → F := mop true
prefix:74 "□" => StandardModalLogicalConnective.box

@[match_pattern]
abbrev dia : F → F := mop false
prefix:74 "◇" => StandardModalLogicalConnective.dia

lemma duality' {p : F} : (◇p) = ~(□(~p)) := by apply StandardModalLogicalConnective.duality

abbrev multibox (n : ℕ) : F → F := (mop true)^[n]
notation:74 "□[" n:90 "]" p:80 => StandardModalLogicalConnective.multibox n p

abbrev multidia (n : ℕ) : F → F := (mop false)^[n]
notation:74 "◇[" n:90 "]" p:80 => StandardModalLogicalConnective.multidia n p

end LO.StandardModalLogicalConnective


section

variable [LO.StandardModalLogicalConnective F] [DecidableEq F]


namespace Set

abbrev multibox (n : ℕ) (s : Set F) : Set F := Set.multimop true n s
notation "□[" n:90 "]" s:80 => Set.multibox n s

abbrev box (s : Set F) : Set F := Set.mop true s
notation "□" s:80 => Set.box s

abbrev premultibox (n : ℕ) (s : Set F) : Set F := Set.premultimop true n s
notation "□⁻¹[" n:90 "]" s:80 => Set.premultibox n s

abbrev prebox (s : Set F) : Set F := Set.premop true s
notation "□⁻¹" s:80 => Set.prebox s

abbrev multidia (n : ℕ) (s : Set F) : Set F := Set.multimop false n s
notation "◇[" n:90 "]" s:80 => Set.multidia n s

abbrev dia (s : Set F) : Set F := Set.mop false s
notation "◇" s:80 => Set.dia s

abbrev premultidia (n : ℕ) (s : Set F) : Set F := Set.premultimop false n s
notation "◇⁻¹[" n:90 "]" s:80 => Set.premultidia n s

abbrev predia (s : Set F) : Set F := Set.premop false s
notation "◇⁻¹" s:80 => Set.predia s

end Set


namespace List

abbrev multibox (n : ℕ) (l : List F) : List F := List.multimop true n l

abbrev box (l : List F) : List F := List.mop true l

abbrev multidia (n : ℕ) (l : List F) : List F := List.multimop false n l

abbrev dia (l : List F) : List F := List.mop false l

end List


namespace Finset

noncomputable abbrev multibox (n : ℕ) (s : Finset F) : Finset F := Finset.multimop true n s
notation "□[" n:90 "]" s:80 => Finset.multibox n s

noncomputable abbrev box (s : Finset F) : Finset F := Finset.mop true s
notation "□" s:80 => Finset.box s

noncomputable abbrev premultibox (n : ℕ) (s : Finset F) : Finset F := Finset.premultimop true n s
notation "□⁻¹[" n:90 "]" s:80 => Finset.premultibox n s

noncomputable abbrev prebox (s : Finset F) : Finset F := Finset.premop true s
notation "□⁻¹" s:80 => Finset.prebox s

noncomputable abbrev multidia (n : ℕ) (s : Finset F) : Finset F := Finset.multimop false n s
notation "◇[" n:90 "]" s:80 => Finset.multidia n s

noncomputable abbrev dia (s : Finset F) : Finset F := Finset.mop false s
notation "◇" s:80 => Finset.dia s

noncomputable abbrev premultidia (n : ℕ) (s : Finset F) : Finset F := Finset.premultimop false n s
notation "◇⁻¹[" n:90 "]" s:80 => Finset.premultidia n s

noncomputable abbrev predia (s : Finset F) : Finset F := Finset.premop false s
notation "◇⁻¹" s:80 => Finset.predia s

end Finset

end
