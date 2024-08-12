import Lean4Less.Commands
import patch.PatchTheoremsAx

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

axiom k : K
axiom B : Bool → Type
axiom hk : B (@K.rec (fun _ => Bool) true k)

-- succeeds because of K-like reduction
-- (do not need constructor application to reduce)
theorem kLikeReduction : B true := hk

-- succeeds because of K-like reduction
-- (do not need constructor application to reduce)
-- theorem kLikeReduction' : B true := 
--    @L4L.castHEq (B (@K.rec (fun (x : K) => Bool) Bool.true k)) (B Bool.true)
--      (@L4L.appArgHEq Bool (fun (a : Bool) => Type) B (@K.rec (fun (x : K) => Bool) Bool.true k) Bool.true
--        (@L4L.appArgHEq K (fun (t : K) => (fun (x : K) => Bool) t) (@K.rec (fun (x : K) => Bool) Bool.true) k K.mk
--          (L4L.prfIrrel K k K.mk)))
--      hk
--
-- def ex' : T q Qq := 
--    @L4L.castHEq (T p Qp) (T q Qq)
--      (@L4L.appHEqABUV (Q p) (Q q) (fun (a : Q p) => Prop) (fun (a : Q q) => Prop)
--        (@L4L.appHEq P (fun (a : P) => Prop) Q Q p q (@HEq.refl (P → Prop) Q) (L4L.prfIrrelHEq P P (@HEq.refl Prop P) p q))
--        (fun (a : Q p) (a_1 : Q q) (a : @HEq (Q p) a (Q q) a_1) => @HEq.refl Type Prop) (T p) (T q) Qp Qq
--        (@L4L.appHEqUV P (fun (p : P) => Q _root_.p → Prop) (fun (p : P) => Q q → Prop)
--          (fun (p : P) =>
--            @L4L.forallHEqAB (Q _root_.p) (Q q) (fun (a : Q _root_.p) => Prop) (fun (a : Q q) => Prop)
--              (@L4L.appHEq P (fun (a : P) => Prop) Q Q _root_.p q (@HEq.refl (P → Prop) Q)
--                (L4L.prfIrrelHEq P P (@HEq.refl Prop P) _root_.p q))
--              fun (a : Q _root_.p) (a_1 : Q q) (a : @HEq (Q _root_.p) a (Q q) a_1) => @HEq.refl Type Prop)
--          T T p q (@HEq.refl ((p : P) → Q p → Prop) T) (L4L.prfIrrelHEq P P (@HEq.refl Prop P) p q))
--        (L4L.prfIrrelHEq (Q p) (Q q)
--          (@L4L.appHEq P (fun (a : P) => Prop) Q Q p q (@HEq.refl (P → Prop) Q)
--            (L4L.prfIrrelHEq P P (@HEq.refl Prop P) p q))
--          Qp Qq))
--      t

example {α : Sort u} {a a' : α} (h : HEq a a') : Eq a a' :=
  have : (α β : Sort u) → (a : α) → (b : β) → HEq a b → (h : Eq α β) → Eq (cast h a) b :=
    fun A B a b h₁ =>
      h₁.rec (fun _ => rfl)
  this α α a a' h rfl

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
