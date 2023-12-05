import Logic.FirstOrder.Arith.PAminus
import Logic.Vorspiel.Arith
import Logic.FirstOrder.Computability.Calculus

namespace LO

namespace FirstOrder

namespace Arith

open Encodable

lemma Hierarchy.equal {t u : Subterm ℒₒᵣ μ n} : Hierarchy b s “!!t = !!u” := by
  simp[Subformula.Operator.operator, Matrix.fun_eq_vec₂,
    Subformula.Operator.Eq.sentence_eq, Subformula.Operator.LT.sentence_eq]

scoped notation: max "⸢" a "⸣" => Subterm.Operator.godelNumber ℒₒᵣ a

open Nat.ArithPart₁

def codeAux : {k : ℕ} → Nat.ArithPart₁.Code k → Formula ℒₒᵣ (Fin (k + 1))
  | _, Code.zero _    => “&0 = 0”
  | _, Code.one _     => “&0 = 1”
  | _, Code.add i j   => “&0 = !!&i.succ + !!&j.succ”
  | _, Code.mul i j   => “&0 = !!&i.succ * !!&j.succ”
  | _, Code.equal i j => “(!!&i.succ = !!&j.succ ∧ &0 = 1) ∨ (!!&i.succ ≠ !!&j.succ ∧ &0 = 0)”
  | _, Code.lt i j    => “(!!&i.succ < !!&j.succ ∧ &0 = 1) ∨ (¬!!&i.succ < !!&j.succ ∧ &0 = 0)”
  | _, Code.proj i    => “&0 = !!&i.succ”
  | _, Code.comp c d  =>
    exClosure (((Rew.bind ![] (&0 :> (#·))).hom (codeAux c)) ⋏
      Matrix.conj fun i => (Rew.bind ![] (#i :> (&·.succ))).hom (codeAux (d i)))
  | _, Code.rfind c   =>
    (Rew.bind ![] (⸢0⸣ :> &0 :> (&·.succ))).hom (codeAux c) ⋏
    (∀[“#0 < &0”] ∃' “#0 ≠ 0” ⋏ (Rew.bind ![] (#0 :> #1 :> (&·.succ))).hom (codeAux c))

def code (c : Code k) : Subsentence ℒₒᵣ (k + 1) := (Rew.bind ![] (#0 :> (#·.succ))).hom (codeAux c)

lemma codeAux_sigma_one {k} (c : Nat.ArithPart₁.Code k) : Hierarchy.Sigma 1 (codeAux c) := by
  induction c <;> simp[codeAux, Subformula.Operator.operator, Matrix.fun_eq_vec₂,
    Subformula.Operator.Eq.sentence_eq, Subformula.Operator.LT.sentence_eq]
  case comp c d ihc ihg =>
    exact Hierarchy.exClosure (by simp; exact ⟨Hierarchy.rew _ ihc, fun i => Hierarchy.rew _ (ihg i)⟩)
  case rfind k c ih =>
    exact ⟨Hierarchy.rew _ ih, by
      suffices : Hierarchy.Sigma 1 (n := 0) (∀[“#0 < &0”] ∃' “#0 ≠ 0” ⋏ (Rew.bind ![] (#0 :> #1 :> (&·.succ))).hom (codeAux c))
      · simpa[Subformula.Operator.operator, Matrix.fun_eq_vec₂,
          Subformula.Operator.Eq.sentence_eq, Subformula.Operator.LT.sentence_eq] using this
      exact Hierarchy.ball' &0 (by simp) (Hierarchy.ex $ by
        simp[Hierarchy.neg_iff, Hierarchy.equal]; exact Hierarchy.rew _ ih)⟩

lemma code_sigma_one {k} (c : Nat.ArithPart₁.Code k) : Hierarchy.Sigma 1 (code c) :=
  Hierarchy.rew _ (codeAux_sigma_one c)

lemma models_codeAux {c : Code k} {f : Vector ℕ k →. ℕ} (hc : c.eval f) (y : ℕ) (v : Fin k → ℕ) :
    Subformula.Val! ℕ (y :> v) (codeAux c) ↔ f (Vector.ofFn v) = Part.some y := by
  induction hc generalizing y <;> simp[code, codeAux, models_iff]
  case zero =>
    have : (0 : Part ℕ) = Part.some 0 := rfl
    simp[this, eq_comm]
  case one =>
    have : (1 : Part ℕ) = Part.some 1 := rfl
    simp[this, eq_comm]
  case equal i j =>
    by_cases hv : v i = v j <;> simp[hv, Nat.isEqNat, eq_comm]
  case lt i j =>
    by_cases hv : v i < v j <;> simp[hv, Nat.isLtNat, eq_comm]
    · simp[Nat.not_le.mpr hv]
    · intro _; exact Nat.not_lt.mp hv
  case add => simp[eq_comm]
  case mul => simp[eq_comm]
  case proj => simp[eq_comm]
  case comp c d f g _ _ ihf ihg =>
    simp[Subformula.eval_rew, Function.comp, Matrix.empty_eq, Matrix.comp_vecCons']
    constructor
    · rintro ⟨e, hf, hg⟩
      have hf : f (Vector.ofFn e) = Part.some y := (ihf _ _).mp hf
      have hg : ∀ i, g i (Vector.ofFn v) = Part.some (e i) := fun i => (ihg i _ _).mp (hg i)
      simp[hg, hf]
    · intro h
      have : ∃ w, (∀ i, Vector.get w i ∈ g i (Vector.ofFn v)) ∧ y ∈ f w := by
        simpa using Part.eq_some_iff.mp h
      rcases this with ⟨w, hw, hy⟩
      exact ⟨w.get, (ihf y w.get).mpr (by simpa[Part.eq_some_iff] using hy),
        fun i => (ihg i (w.get i) v).mpr (by simpa[Part.eq_some_iff] using hw i)⟩
  case rfind c f _ ihf =>
    simp[Subformula.eval_rew, Function.comp, Matrix.empty_eq, Matrix.comp_vecCons', ihf, Vector.ofFn_vecCons]
    constructor
    · rintro ⟨hy, h⟩; simp[Part.eq_some_iff]
      exact ⟨by simpa using hy, by intro z hz; simpa using h z hz⟩
    · intro h; simpa using Nat.mem_rfind.mp (Part.eq_some_iff.mp h)

lemma models_code {c : Code k} {f : Vector ℕ k →. ℕ} (hc : c.eval f) (y : ℕ) (v : Fin k → ℕ) :
    Subformula.PVal! ℕ (y :> v) (code c) ↔ y ∈ f (Vector.ofFn v) := by
  simpa[code, models_iff, Subformula.eval_rew, Matrix.empty_eq, Function.comp,
    Matrix.comp_vecCons', ←Part.eq_some_iff] using models_codeAux hc y v

noncomputable def codeOfPartrec {k} (f : Vector ℕ k →. ℕ) : Code k :=
  Classical.epsilon (fun c => ∀ y v, Subformula.PVal! ℕ (y :> v) (code c) ↔ y ∈ f (Vector.ofFn v))

lemma codeOfPartrec_spec {k} {f : Vector ℕ k →. ℕ} (hf : Nat.Partrec' f) {y : ℕ} {v : Fin k → ℕ} :
    Subformula.PVal! ℕ (y :> v) (code $ codeOfPartrec f) ↔ y ∈ f (Vector.ofFn v) := by
  have : ∃ c, ∀ y v, Subformula.PVal! ℕ (y :> v) (code c) ↔ y ∈ f (Vector.ofFn v) := by
    rcases Nat.ArithPart₁.exists_code (of_partrec hf) with ⟨c, hc⟩
    exact ⟨c, models_code hc⟩
  exact Classical.epsilon_spec this y v

variable {T : Theory ℒₒᵣ} [EqTheory T] [PAminus T] [DecidablePred T] [SigmaOneSound T] [Theory.Computable T]

section representation

lemma provable_iff_mem_partrec {k} {f : Vector ℕ k →. ℕ} (hf : Nat.Partrec' f) {y : ℕ} {v : Fin k → ℕ} :
    (T ⊢! (Rew.substs $ ⸢y⸣ :> fun i => ⸢v i⸣).hom (code $ codeOfPartrec f)) ↔ y ∈ f (Vector.ofFn v) := by
  let σ : Sentence ℒₒᵣ := (Rew.substs $ ⸢y⸣ :> fun i => ⸢v i⸣).hom (code $ codeOfPartrec f)
  have sigma : Hierarchy.Sigma 1 σ :=
    (Hierarchy.rew (Rew.substs $ ⸢y⸣ :> fun i => ⸢v i⸣) (code_sigma_one (codeOfPartrec f)))
  constructor
  · rintro ⟨b⟩
    have : Subformula.PVal! ℕ (y :> v) (code $ codeOfPartrec f) := by
      simpa[models_iff, Subformula.eval_rew, Matrix.empty_eq, Function.comp, Matrix.comp_vecCons'] using
        Arith.Sound.sound sigma ⟨b⟩
    exact (codeOfPartrec_spec hf).mp this
  · intro h
    exact ⟨PAminus.sigma_one_completeness sigma (by
      simp[models_iff, Subformula.eval_rew, Matrix.empty_eq,
        Function.comp, Matrix.comp_vecCons', codeOfPartrec_spec hf, h])⟩

variable {α : Type*} {σ : Type*} [Primcodable α] [Primcodable σ]

noncomputable def graph (f : α →. σ) : Subsentence ℒₒᵣ 2 :=
  code (codeOfPartrec fun x => Part.bind (decode (α := α) x.head) fun a => (f a).map encode)

theorem representation {f : α →. σ} (hf : Partrec f) {x y} :
    T ⊢! (graph f)/[⸢y⸣, ⸢x⸣] ↔ y ∈ f x := by
  let f' : Vector ℕ 1 →. ℕ := fun x => Part.bind (decode (α := α) x.head) fun a => (f a).map encode
  have : Nat.Partrec' f' :=
    Nat.Partrec'.part_iff.mpr
      (Partrec.bind (Computable.ofOption $ Primrec.to_comp $ Primrec.decode.comp Primrec.vector_head)
      (Partrec.to₂ <| Partrec.map (hf.comp .snd) (Computable.encode.comp₂ .right)))
  simpa[Matrix.constant_eq_singleton] using
    provable_iff_mem_partrec this (y := encode y) (v := ![encode x])

noncomputable def pred (p : α → Prop) : Subsentence ℒₒᵣ 1 :=
  (graph (fun a => Part.assert (p a) fun _ => Part.some ()))/[⸢()⸣, #0]

theorem pred_representation {p : α → Prop} (hp : RePred p) {x} :
    T ⊢! (pred p)/[⸢x⸣] ↔ p x := by
  simpa[pred, ←Rew.hom_comp_app, Rew.substs_comp_substs] using
    representation hp (T := T) (x := x) (y := ())

variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]
  [(k : ℕ) → Primcodable (L.func k)] [(k : ℕ) → Primcodable (L.rel k)]
  [UniformlyPrimcodable L.func] [UniformlyPrimcodable L.rel]

noncomputable def provableSentence (U : Theory L) : Subsentence ℒₒᵣ 1 := pred (U ⊢! ·)

theorem provableSentence_representation (U : Theory L) [DecidablePred U] [Theory.Computable U] {σ} :
    T ⊢! (provableSentence U)/[⸢σ⸣] ↔ U ⊢! σ := by
  simpa using pred_representation (T := T) (provable_RePred U) (x := σ)

end representation

end Arith

end FirstOrder

end LO