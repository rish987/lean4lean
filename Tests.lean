import Lean4Less.Commands
import patch.PatchTheorems

axiom P : Prop
axiom Q : P → Prop
axiom p : P
axiom q : P
axiom Qp : Q p
axiom Qq : Q q

axiom T : (p : P) → Q p → Prop

axiom t : T p Qp

-- with proof irrelevance, `t` would suffice
def ex : T q Qq := t

#check_l4l ex

-- axiom T : Type → Type
-- axiom t : T Prop
--
-- unsafe def test : Nat → Type
-- | .zero => Prop
-- | .succ _ => (fun (x : T (test .zero)) => Bool) t
--
-- mutual
--   def test1 : Nat → Type
--   | .zero => Prop
--   | .succ _ => (fun (x : T (test2 .zero)) => Bool) t
--   def test2 : Nat → Type
--   | .zero => Prop
--   | .succ _ => (fun (x : T (test1 .zero)) => Bool) t
-- end
