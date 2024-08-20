import Lean4Less.Commands
import patch.PatchTheoremsAx

universe u v

axiom P : Prop
axiom Q : P → Prop
axiom p : P
axiom q : P

axiom X : (p : P) → Q p → Q p

def forallEx : Q q → Q q := fun (qp : Q p) => X p qp 

def forallEx' : Q q → Q q :=
@L4L.castHEq (Q p → Q p) (Q q → Q q)
  (@L4L.forallHEqAB (Q p) (Q q) (Q p) (Q q) (@L4L.appArgHEq P Prop Q p q (L4L.prfIrrel P p q))
    (@L4L.appArgHEq P Prop Q p q (L4L.prfIrrel P p q)))
  fun (qp : Q p) => X p qp
def forallEx'' : Q q → Q q :=
  fun (qq : Q q) => @L4L.castHEq (Q p) (Q q) (@L4L.appArgHEq P Prop Q p q (L4L.prfIrrel P p q))
                      (X p (@L4L.castHEq (Q q) (Q p) (@L4L.appArgHEq P Prop Q q p (L4L.prfIrrel P q p)) qq)) 
#check_off forallEx''

axiom Qp : Q p
axiom Qq : Q q

axiom T : (p : P) → Q p → Prop

axiom t : T p Qp

-- with proof irrelevance, `t` would suffice
def nestedPrfIrrelTest : T q Qq := t

inductive K : Prop where
  | mk : K
-- K.rec.{u} {a b : Nat}
--   {motive : (c : Nat) → K a b c → Sort u} 
--   (mk : motive 0 (K.mk a b)) {c : Nat}
--   (t : K a b c) : motive c t

axiom k : K 
axiom BK : Bool → Type
axiom hk : BK (@K.rec (fun _ => Bool) true k)

-- succeeds because of K-like reduction
-- (do not need constructor application to reduce)
noncomputable def kLikeReduction : BK true := hk

axiom A : Type
axiom a : A
axiom h : Eq A A
-- axiom R : BK true → P → Prop
theorem aux (α β : Sort u) (a : α) (b : β) (h₁ : HEq a b) : (h : Eq α β) → Eq (cast h a) b :=
  h₁.rec (fun _ => rfl)
axiom aux' : (α β : Sort u) → (a : α) → (b : β) → HEq a b → (h : Eq α β) → Eq (cast h a) b

def letFun' {α : Sort u} {β : α → Sort v} (v : α) (f : (x : α) → β x) : β v := f v

-- axiom ax' : (@Eq.rec (Type 1) Type (fun (x : Type 1) (x_1 : @Eq (Type 1) Type x) => x) n Type axh)
-- axiom axHEq : HEq axh (@Eq.refl (Type 1) Type)
-- -- axiom ax (α : Sort u) (a : α) : BK (@K.rec (fun _ => Bool) true k)
-- -- axiom ax' (α : Sort u) (a : α) : BK true → (a' : α) → cast (axh α α) a = a'
-- axiom Ty : Type
-- axiom ty : Ty
-- 
-- noncomputable def eq_of_heq' : cast axh n :=
--   ax'
-- -#check_l4l eq_of_heq

axiom n : Type
axiom n' : Type
axiom axh : Type = Type
axiom ax : cast axh n
axiom ax' : n → Prop
-- axiom ax (α : Sort u) (a : α) : BK (@K.rec (fun _ => Bool) true k)
-- axiom ax' (α : Sort u) (a : α) : BK true → (a' : α) → cast (axh α α) a = a'
axiom Ty : Type
axiom ty : Ty
noncomputable def eq_of_heq' : Prop :=
  ax' ax 
-- #check_l4l eq_of_heq'
-- set_option pp.explicit true in
-- #print eq_of_heq'

-- def ex : ∀ x : P, (@dite Prop P (.isTrue x) (fun p => Q p) (fun p => True)) := fun x => Qq

-- #print ex
axiom L : (p : P) → ((q : Q p) → Q p) → Type
axiom l : L q fun qq : Q q => qq

axiom M1 : {P : Prop} → P → Type
axiom M2 : {P Q : Prop} → P → Q → Type

axiom L' : (P Q : Prop) → ((p : P) → (q : Q) → Type) → Type

noncomputable def lamTest : L p fun qp : Q p => qp := l

axiom l1 : L' (Q q) (Q q) fun _qq qq' : Q q => M1 qq'
axiom l2 : L' (Q q) (Q q) fun qq qq' : Q q => M2 qq qq'
noncomputable def lamTest1 : L' (Q p) (Q q) fun _qp qq => M1 qq := l1
noncomputable def lamTest2 : L' (Q p) (Q q) fun qp qq => M2 qp qq := l2

set_option pp.all true
-- #print if_pos.match_1
#check_only lamTest
-- #check_l4l ex
-- #check_l4l ex
-- #print Fin.mk_zero
-- #check_l4l Fin.mk_zero

-- #check_l4l kLikeReduction
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

axiom G : P → Type
axiom H : (p : P) → G p → Type
axiom H.mk : (p : P) → (g : G p) → H p g

noncomputable def pushTest : (g : G q) → H q g := fun (g : G p) => H.mk p g

def F : Bool → Type
| true => Bool
| _ => Unit

structure S : Type where
b : Bool
f : F b

#check S.mk

axiom B : Bool → Type
axiom B.mk : (b : Bool) → B b

axiom s : B (@K.rec (fun _ => S) (S.mk true true) k).2
noncomputable def projTest : B (S.mk true true).2 := s
#check_l4l projTest
