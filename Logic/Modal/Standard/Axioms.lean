import Logic.Modal.LogicSymbol

namespace LO

variable {F : Type*} [LogicalConnective F] [StandardModalLogicalConnective F]

namespace Axioms

variable (p q r : F)

protected abbrev K := □(p ⟶ q) ⟶ □p ⟶ □q
abbrev K.set : Set F := { Axioms.K p q | (p) (q) }
notation "⟮K⟯" => K.set

protected abbrev T := □p ⟶ p
abbrev T.set : Set F := { Axioms.T p | (p) }
notation "⟮T⟯" => T.set

protected abbrev B := p ⟶ □◇p
abbrev B.set : Set F := { Axioms.B p | (p) }
notation "⟮B⟯" => B.set

protected abbrev D := □p ⟶ ◇p
abbrev D.set : Set F := { Axioms.D p | (p) }
notation "⟮D⟯" => D.set

protected abbrev Four := □p ⟶ □□p
abbrev Four.set : Set F := { Axioms.Four p | (p) }
notation "⟮4⟯" => Four.set

protected abbrev Five := ◇p ⟶ □◇p
abbrev Five.set : Set F := { Axioms.Five p | (p) }
notation "⟮5⟯" => Five.set

protected abbrev Dot2 := ◇□p ⟶ □◇p

protected abbrev C4 := □□p ⟶ □p

protected abbrev CD := ◇p ⟶ □p

protected abbrev Tc := p ⟶ □p
abbrev Tc.set : Set F := { Axioms.Tc p | (p) }
notation "⟮Tc⟯" => Tc.set

protected abbrev Ver := □p
abbrev Ver.set : Set F := { Axioms.Ver p | (p) }
notation "⟮Ver⟯" => Ver.set

protected abbrev Dot3 := □(□p ⟶ q) ⋎ □(□q ⟶ p)

protected abbrev Grz := □(□(p ⟶ □p) ⟶ p) ⟶ p

protected abbrev M := (□◇p ⟶ ◇□p)

protected abbrev L := □(□p ⟶ p) ⟶ □p
abbrev L.set : Set F := { Axioms.L p | (p) }
notation "⟮L⟯" => L.set

protected abbrev H := □(□p ⟷ p) ⟶ □p
abbrev H.set : Set F := { Axioms.H p | (p) }
notation "⟮H⟯" => H.set

end Axioms

end LO
