import Logic.Logic.System

namespace LO

variable {F : Type*} [LogicalConnective F]

namespace Axioms

variable (p q r : F)

protected abbrev Verum : F := ⊤
abbrev Verum.set : Set F := { Axioms.Verum }
notation "⟮⊤⟯" => Verum.set

protected abbrev Imply₁ := p ⟶ q ⟶ p
abbrev Imply₁.set : Set F := { Axioms.Imply₁ p q | (p) (q) }
notation "⟮⟶₁⟯" => Imply₁.set

protected abbrev Imply₂ := (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r
abbrev Imply₂.set : Set F := { Axioms.Imply₂ p q r | (p) (q) (r) }
notation "⟮⟶₂⟯" => Imply₂.set

protected abbrev AndElim₁ := p ⋏ q ⟶ p
abbrev AndElim₁.set : Set F := { Axioms.AndElim₁ p q | (p) (q) }
notation "⟮⋏E₁⟯" => AndElim₁.set

protected abbrev AndElim₂ := p ⋏ q ⟶ q
abbrev AndElim₂.set : Set F := { Axioms.AndElim₂ p q | (p) (q) }
notation "⟮⋏E₂⟯" => AndElim₂.set

protected abbrev AndInst := p ⟶ q ⟶ p ⋏ q
abbrev AndInst.set : Set F := { Axioms.AndInst p q | (p) (q) }
notation "⟮⋏I⟯" => AndInst.set

protected abbrev OrInst₁ := p ⟶ p ⋎ q
abbrev OrInst₁.set : Set F := { Axioms.OrInst₁ p q | (p) (q) }
notation "⟮⋎I₁⟯" => OrInst₁.set

protected abbrev OrInst₂ := q ⟶ p ⋎ q
abbrev OrInst₂.set : Set F := { Axioms.OrInst₂ p q | (p) (q) }
notation "⟮⋎I₂⟯" => OrInst₂.set

protected abbrev OrElim := (p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)
abbrev OrElim.set : Set F := { Axioms.OrElim p q r | (p) (q) (r) }
notation "⟮⋎E⟯" => OrElim.set

protected abbrev NegEquiv := ~p ⟷ (p ⟶ ⊥)
abbrev NegEquiv.set : Set F := { Axioms.NegEquiv p | (p) }
notation "⟮~⟯" => NegEquiv.set

protected abbrev EFQ := ⊥ ⟶ p
abbrev EFQ.set : Set F := { Axioms.EFQ p | (p) }
notation "⟮EFQ⟯" => EFQ.set

protected abbrev LEM := p ⋎ ~p
abbrev LEM.set : Set F := { Axioms.LEM p | (p) }
notation "⟮LEM⟯" => LEM.set

protected abbrev WeakLEM := ~p ⋎ ~~p
abbrev WeakLEM.set : Set F := { Axioms.WeakLEM p | (p) }
notation "⟮WEM⟯" => WeakLEM.set

protected abbrev GD := (p ⟶ q) ⋎ (q ⟶ p)
abbrev GD.set : Set F := { Axioms.GD p q | (p) (q) }
notation "⟮GD⟯" => GD.set

protected abbrev DNE := ~~p ⟶ p
abbrev DNE.set : Set F := { Axioms.DNE p | (p) }
notation "⟮DNE⟯" => DNE.set

protected abbrev Peirce := ((p ⟶ q) ⟶ p) ⟶ p
abbrev Peirce.set : Set F := { Axioms.Peirce p q | (p) (q) }
notation "⟮Peirce⟯" => Peirce.set

end Axioms

end LO
