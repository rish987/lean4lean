prelude
import Init.Prelude
import Init.Notation
import Init.Core

namespace L4L

universe u v

axiom prfIrrel {P : Prop} (p q : P) : HEq p q
axiom prfIrrelHEq {P Q : Prop} (heq : HEq P Q) (p : P) (q : Q) : HEq p q

#print eq_of_heq
axiom eq_of_heq {α : Sort u} {a a' : α} (h : HEq a a') : Eq a a'

def castHEq (α β : Sort u) (h : HEq α β) (a : α) : β := cast (eq_of_heq h) a

axiom castOrigHEq {α β : Sort u} : (h : HEq α β) → (a : α) → HEq (castHEq _ _ h a) a

def HEqRefl (n : Nat) {α : Sort u} (a : α) : HEq a a := HEq.refl a

axiom forallHEqUV {A : Sort u} {U V : Sort v}
  (hUV : HEq U V)
  : HEq ((a : A) → U) ((b : A) → V)

axiom forallHEqUV' {A : Sort u} {U V : A → Sort v}
  (hUV : (a : A) → HEq (U a) (V a))
  : HEq ((a : A) → U a) ((b : A) → V b)

axiom forallEqUV' {A : Sort u} {U V : A → Sort v}
  (hUV : (a : A) → Eq (U a) (V a))
  : Eq ((a : A) → U a) ((b : A) → V b)

axiom forallHEqAB {A B : Sort u} {U : Sort v} (hAB : HEq A B)
  : HEq ((a : A) → U) ((b : B) → U)

axiom forallHEqABUV {A B : Sort u} {U V : Sort v}
  (hAB : HEq A B) (hUV : HEq U V)
  : HEq ((a : A) → U) ((b : B) → V)

axiom forallEqAB {A B : Sort u} {U : Sort v}
  (hAB : Eq A B)
  : Eq ((a : A) → U) ((b : B) → U)

axiom forallEqABUV {A B : Sort u} {U V : Sort v}
  (hAB : Eq A B) (hUV : Eq U V)
  : Eq ((a : A) → U) ((b : B) → V)

axiom forallHEqABUV' {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (hAB : HEq A B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
  : HEq ((a : A) → U a) ((b : B) → V b)

axiom forallEqABUV' {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (hAB : Eq A B) (hUV : (a : A) → (b : B) → HEq a b → Eq (U a) (V b))
  : Eq ((a : A) → U a) ((b : B) → V b)

axiom appArgHEq {A : Sort u} {U : Sort v}
  (f : (a : A) → U)
  {a b : A} (hab : HEq a b)
  : HEq (f a) (f b)

axiom appArgEq {A : Sort u} {U : Sort v}
  (f : (a : A) → U)
  {a b : A} (hab : Eq a b)
  : Eq (f a) (f b)

axiom appArgHEq' {A : Sort u} {U : A → Sort v}
  (f : (a : A) → U a)
  (a b : A) (hab : HEq a b)
  : HEq (f a) (f b)

axiom appFunHEq {A : Sort u} {U : Sort v}
  {f g : (a : A) → U} (a : A)
  (hfg : HEq f g)
  : HEq (f a) (g a)

axiom appFunEq {A : Sort u} {U : Sort v}
  {f g : (a : A) → U} (a : A)
  (hfg : Eq f g)
  : Eq (f a) (g a)

axiom appFunHEq' {A : Sort u} {U : A → Sort v}
  {f g : (a : A) → U a} (a : A)
  (hfg : HEq f g)
  : HEq (f a) (g a)

axiom appFunEq' {A : Sort u} {U : A → Sort v}
  {f g : (a : A) → U a} (a : A)
  (hfg : Eq f g)
  : Eq (f a) (g a)

axiom appHEq {A : Sort u} {U : Sort v}
  {f g : (a : A) → U} {a b : A}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b)

axiom appEq {A : Sort u} {U : Sort v}
  {f g : A → U} {a b : A}
  (hfg : Eq f g) (hab : Eq a b)
  : Eq (f a) (g b)

axiom appHEq' {A : Sort u} {U : A → Sort v}
  {f g : (a : A) → U a} {a b : A}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b)

axiom appFunHEqUV {A : Sort u} {U V : Sort v}
  (hUV : HEq U V)
  {f : (a : A) → U} {g : (b : A) → V} (a : A) 
  (hfg : HEq f g)
  : HEq (f a) (g a)

axiom appFunHEqUV' {A : Sort u} {U V : A → Sort v}
  (hUV : (a : A) → HEq (U a) (V a))
  {f : (a : A) → U a} {g : (b : A) → V b} (a : A) 
  (hfg : HEq f g)
  : HEq (f a) (g a)

axiom appHEqUV {A : Sort u} {U V : Sort v}
  (hUV : HEq U V)
  {f : (a : A) → U} {g : (b : A) → V} {a : A} {b : A}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b)

axiom appHEqUV' {A : Sort u} {U V : A → Sort v}
  (hUV : (a : A) → HEq (U a) (V a))
  {f : (a : A) → U a} {g : (b : A) → V b} {a : A} {b : A}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b)

axiom appHEqAB {A B : Sort u} {U : Sort v}
  (hAB : HEq A B)
  {f : (a : A) → U} {g : (b : B) → U} {a : A} {b : B}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b)

axiom appEqAB {A B : Sort u} {U : Sort v}
  (hAB : Eq A B)
  {f : (a : A) → U} {g : (b : B) → U} {a : A} {b : B}
  (hfg : HEq f g) (hab : HEq a b)
  : Eq (f a) (g b)

axiom appHEqABUV {A B : Sort u} {U V : Sort v}
  (hAB : HEq A B) (hUV : HEq U V)
  {f : (a : A) → U} {g : (b : B) → V} {a : A} {b : B}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b)

axiom appHEqABUV' {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (hAB : HEq A B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
  {f : (a : A) → U a} {g : (b : B) → V b} {a : A} {b : B}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b)

#print Exists.rec

axiom appAbsHEqABUV' {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (hAB : HEq A B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
  {f : (a : A) → U a} {g : (b : B) → V b} {a : A} {b : B}
  (hfg : (a : A) → (b : B) → HEq a b → HEq (f a) (g b)) (hab : HEq a b)
  : HEq (f a) (g b)

axiom appHEqBinNatFn {N : Type} {T : Type}
  {f : N → N → T} {a1 a2 : N} {b1 b2 : N}
  (ha : HEq a1 a2)
  (hb : HEq b1 b2)
  : HEq (f a1 b1) (f a2 b2)

axiom lambdaHEq {A : Sort u} {U : Sort v}
  (f g : (a : A) → U)
  (hfg : (a : A) → HEq (f a) (g a))
  : HEq (fun a => f a) (fun b => g b)

axiom lambdaEq {A : Sort u} {U : Sort v}
  (f g : (a : A) → U)
  (hfg : (a : A) → Eq (f a) (g a))
  : Eq (fun a => f a) (fun b => g b)

axiom lambdaHEq' {A : Sort u} {U : A → Sort v}
  (f g : (a : A) → U a)
  (hfg : (a : A) → HEq (f a) (g a))
  : HEq (fun a => f a) (fun b => g b)

axiom lambdaEq' {A : Sort u} {U : A → Sort v}
  (f g : (a : A) → U a)
  (hfg : (a : A) → Eq (f a) (g a))
  : Eq (fun a => f a) (fun b => g b)

axiom lambdaHEqUV {A : Sort u} {U V : Sort v}
  (f : (a : A) → U) (g : (b : A) → V)
  (hfg : (a : A) → HEq (f a) (g a))
  : HEq (fun a => f a) (fun b => g b)

axiom lambdaHEqUV' {A : Sort u} {U V : A → Sort v}
  (f : (a : A) → U a) (g : (b : A) → V b)
  (hfg : (a : A) → HEq (f a) (g a))
  : HEq (fun a => f a) (fun b => g b)

axiom lambdaHEqABUV {A B : Sort u} {U V : Sort v}
  (f : (a : A) → U) (g : (b : B) → V)
  (hAB : HEq A B) (hfg : (a : A) → (b : B) → HEq a b → HEq (f a) (g b))
  : HEq (fun a => f a) (fun b => g b)

axiom lambdaHEqABUV' {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (f : (a : A) → U a) (g : (b : B) → V b)
  (hAB : HEq A B) (hfg : (a : A) → (b : B) → HEq a b → HEq (f a) (g b))
  : HEq (fun a => f a) (fun b => g b)

end L4L
