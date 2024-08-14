import Lean4Less.Commands
import patch.PatchTheoremsAx

universe u v

axiom P : Prop
axiom Q : P → Prop
axiom p : P
axiom q : P
axiom Qp : Q p
axiom Qq : Q q

axiom T : (p : P) → Q p → Prop

axiom t : T p Qp

-- with proof irrelevance, `t` would suffice
def nestedPrfIrrel : T q Qq := t

inductive K : Prop where
  | mk : K
-- K.rec.{u} {a b : Nat}
--   {motive : (c : Nat) → K a b c → Sort u} 
--   (mk : motive 0 (K.mk a b)) {c : Nat}
--   (t : K a b c) : motive c t

def k : K := (fun k => k) K.mk
axiom BK : Bool → Type
axiom hk : BK (@K.rec (fun _ => Bool) true k)

-- succeeds because of K-like reduction
-- (do not need constructor application to reduce)
noncomputable def kLikeReduction : BK true := hk

axiom A : Type
axiom a : A
axiom h : Eq A A
axiom h' : ∀ n : Nat, Q q
theorem aux : (α β : Sort u) → (a : α) → (b : β) → HEq a b → (h : Eq α β) → Eq (cast h a) b :=
  fun _ _ _ _ h₁ =>
    h₁.rec (fun _ => rfl)
axiom aux' : (α β : Sort u) → (a : α) → (b : β) → HEq a b → (h : Eq α β) → Eq (cast h a) b

def letFun' {α : Sort u} {β : α → Sort v} (v : α) (f : (x : α) → β x) : β v := f v

theorem eq_of_heq' : ∀ {α : Sort u} {a a' : α}, @HEq α a α a' → @Eq α a a' :=
   fun {α} {a a'} h =>
     letFun' (fun α β a b h₁ =>
       @HEq.rec α a (fun {B : Sort u} b _ => ∀ (h : @Eq (Sort u) α B), @Eq B (@cast α B h a) b)
         (fun x => @rfl α (@cast α α x a)) β b h₁)
     fun this => this α α a a' h (@rfl (Sort u) α)
set_option pp.explicit true in

#print eq_of_heq'

noncomputable def ex : Q q :=
  letFun' (α := Q p) Qq
  fun this => this

-- #print ex

set_option pp.all true
-- #check_off dif_pos
#check_l4l ex
-- #check_only Fin.mk_zero

#check_l4l kLikeReduction
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
