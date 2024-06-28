
import Logic.Vorspiel.Vorspiel

class Collection (β : outParam Type*) (α : Type*) extends Membership β α, HasSubset α, EmptyCollection α, Singleton β α where
  subset_iff {a b : α} : a ⊆ b ↔ ∀ x ∈ a, x ∈ b
  not_mem_empty (x : β) : x ∉ (∅ : α)
  mem_singleton {x z : β} : x ∈ ({z} : α) ↔ x = z

attribute [simp] Collection.not_mem_empty

instance Set.collection : Collection α (Set α) where
  subset_iff := iff_of_eq Set.subset_def
  not_mem_empty := by simp
  mem_singleton := by simp

instance List.collection : Collection α (List α) where
  subset_iff := List.subset_def
  not_mem_empty := by simp
  mem_singleton := by simp [List.singleton_eq]

instance Multiset.collection : Collection α (Multiset α) where
  subset_iff := Multiset.subset_iff
  not_mem_empty := by simp
  mem_singleton := by simp

instance Finset.collection [DecidableEq α] : Collection α (Finset α) where
  subset_iff := Finset.subset_iff
  not_mem_empty := by simp
  mem_singleton := by simp

namespace Option

variable {α : Type*}

inductive Subset : Option α → Option α → Prop where
  | none_none : Subset none none
  | none_some (a : α) : Subset none (some a)
  | some_some (a : α) : Subset (some a) (some a)

instance : HasSubset (Option α) := ⟨Subset⟩

@[simp] lemma none_subset (o : Option α) : none ⊆ o := by
  cases o
  · exact Subset.none_none
  · exact Subset.none_some _

@[simp, refl] lemma Subset.refl (o : Option α) : o ⊆ o := by
  cases o
  · exact Subset.none_none
  · exact Subset.some_some _

@[simp] lemma some_subset_some_iff {a b : α} : some a ⊆ some b ↔ a = b := by
  constructor
  · rintro ⟨⟩; rfl
  · rintro rfl; rfl

@[trans] lemma Subset.trans {o₁ o₂ o₃ : Option α} : o₁ ⊆ o₂ → o₂ ⊆ o₃ → o₁ ⊆ o₃ := by
  rintro ⟨⟩ ⟨⟩ <;> simp

lemma subset_iff {o₁ o₂ : Option α} : o₁ ⊆ o₂ ↔ ∀ x ∈ o₁, x ∈ o₂ := by
  cases o₁ <;> cases o₂ <;> simp [eq_comm]
  · rintro ⟨⟩

instance : EmptyCollection (Option α) := ⟨none⟩

lemma empty_def : (∅ : Option α) = none := rfl

instance : Singleton α (Option α) := ⟨some⟩

lemma singleton_def (a : α) : ({a} : Option α) = some a := rfl

end Option

instance Option.collection : Collection α (Option α) where
  subset_iff := by simp [Option.subset_iff]
  not_mem_empty := by simp
  mem_singleton := by simp [singleton_def, eq_comm]

class Cons (β : outParam Type*) (α : Type*) [Membership β α] where
  cons : β → α → α
  mem_cons_iff {x z : β} {a : α} : x ∈ cons z a ↔ x = z ∨ x ∈ a

attribute [simp] Cons.mem_cons_iff

export Cons (cons)

instance (α : Type*) : Cons α (Set α) := ⟨insert, by simp⟩

instance (α : Type*) : Cons α (List α) := ⟨List.cons, by simp⟩

instance (α : Type*) : Cons α (Multiset α) := ⟨Multiset.cons, by simp⟩

instance (α : Type*) [DecidableEq α] : Cons α (Finset α) := ⟨insert, by simp⟩

namespace Collection

variable {β α : Type*} [Collection β α] [Cons β α]

def set : α → Set β := fun a ↦ {x | x ∈ a}

@[simp] lemma mem_set_iff {x : β} {a : α} : x ∈ (set a : Set β) ↔ x ∈ a := by simp [set]

lemma subset_iff_set_subset_set {a b : α} : a ⊆ b ↔ set a ⊆ set b := by simp [subset_iff, set]

@[simp, refl] lemma subset_refl (a : α) : a ⊆ a := subset_iff_set_subset_set.mpr (Set.Subset.refl _)

@[trans] lemma subset_trans {a b c : α} (ha : a ⊆ b) (hb : b ⊆ c) : a ⊆ c :=
  subset_iff_set_subset_set.mpr (Set.Subset.trans (subset_iff_set_subset_set.mp ha) (subset_iff_set_subset_set.mp hb))

lemma subset_antisymm {a b : α} (ha : a ⊆ b) (hb : b ⊆ a) : set a = set b :=
  Set.Subset.antisymm (subset_iff_set_subset_set.mp ha) (subset_iff_set_subset_set.mp hb)

@[simp] lemma empty_subset (a : α) : ∅ ⊆ a := by simp [subset_iff]

@[simp] lemma mem_cons (a : α) (x : β) : x ∈ cons x a := by simp

@[simp] lemma subset_cons (a : α) (x : β) : a ⊆ cons x a := by simp [subset_iff]; tauto

@[simp] lemma set_empty : set (∅ : α) = ∅ := by ext; simp [set]

@[simp] lemma set_cons (z : β) (a : α) : set (cons z a) = insert z (set a) := by ext; simp [set]

def Finite (a : α) : Prop := (set a).Finite

@[simp] lemma empty_finite : Finite (∅ : α) := by simp [Finite]

lemma Finite.of_subset {a b : α} (ha : Finite a) (h : b ⊆ a) : Finite b :=
  Set.Finite.subset ha (subset_iff_set_subset_set.mp h)

@[simp] lemma cons_finite_iff {z : β} {a : α} : Finite (cons z a) ↔ Finite a :=
  ⟨fun h ↦ h.of_subset (by simp), by simpa [Finite] using Set.Finite.insert z⟩

def addList (a : α) : List β → α
  | [] => a
  | x :: xs => cons x (addList a xs)

def _root_.List.toCollection : List β → α
  | [] => ∅
  | x :: xs => cons x xs.toCollection

noncomputable def _root_.Finset.toCollection : Finset β → α := fun s ↦ s.toList.toCollection

@[simp] lemma mem_list_toCollection {x : β} {l : List β} : x ∈ (l.toCollection : α) ↔ x ∈ l := by
  induction l <;> simp [List.toCollection, *]

@[simp] lemma mem_finset_toCollection {x : β} {s : Finset β} : x ∈ (s.toCollection : α) ↔ x ∈ s := by simp [Finset.toCollection]

@[simp] lemma list_toCollection_finite (l : List β) : Finite (l.toCollection : α) := by simp [Finite, set]

@[simp] lemma finset_toCollection_finite (s : Finset β) : Finite (s.toCollection : α) := by simp [Finite, set]

end Collection

namespace Set

variable {α : Type*}

lemma cons_eq (a : α) (s : Set α) : cons a s = insert a s := rfl

@[simp] lemma collection_set (s : Set α) : Collection.set s = s := rfl

@[simp] lemma collection_finite_iff (s : Set α) : Collection.Finite s ↔ s.Finite := by simp [Collection.Finite]

end Set
