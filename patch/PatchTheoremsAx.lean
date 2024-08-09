prelude
import Init.Prelude
import Init.Notation
import Init.Core

namespace L4L

universe u v

axiom castHEq {α β : Sort u} (h : HEq α β) (a : α) : β

axiom forallHEq {A : Sort u} {U V : A → Sort v}
  (hUV : (a : A) → HEq (U a) (V a))
  : HEq ((a : A) → U a) ((b : A) → V b)

axiom forallHEqAB {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (hAB : HEq A B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
  : HEq ((a : A) → U a) ((b : B) → V b)

axiom prfIrrelHEq (P Q : Prop) (heq : HEq P Q) (p : Q) (q : P) : HEq p q

axiom appArgHEq {A : Sort u} {U : A → Sort v}
  (f : (a : A) → U a)
  {a b : A} (hab : HEq a b)
  : HEq (f a) (f b)

-- axiom forallHEq {A B : Sort u} {U : A → Sort v} {V : B → Sort v} (hAB : A = B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
--   : ((a : A) → U a) = ((b : B) → V b)

axiom appHEq {A : Sort u} {U : A → Sort v}
  {f g : (a : A) → U a} {a b : A}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b)

axiom appHEqUV {A : Sort u} {U V : A → Sort v}
  (hUV : (a : A) → HEq (U a) (V a))
  {f : (a : A) → U a} {g : (b : A) → V b} {a : A} {b : A}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b)

axiom appHEqABUV {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (hAB : HEq A B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
  {f : (a : A) → U a} {g : (b : B) → V b} {a : A} {b : B}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b)

axiom appHEqBinNatFn {N : Type} {T : Type}
  {f : N → N → T} {a1 a2 : N} {b1 b2 : N}
  (ha : HEq a1 a2)
  (hb : HEq b1 b2)
  : HEq (f a1 b1) (f a2 b2)

axiom lambdaHEq {A : Sort u} {U V : A → Sort v}
  (f : (a : A) → U a) (g : (b : A) → V b)
  (hfg : (a : A) → HEq (f a) (g a))
  : HEq (fun a => f a) (fun b => g b)

axiom lambdaHEqAB {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (f : (a : A) → U a) (g : (b : B) → V b)
  (hAB : HEq A B) (hfg : (a : A) → (b : B) → HEq a b → HEq (f a) (g b))
  : HEq (fun a => f a) (fun b => g b)

end L4L
