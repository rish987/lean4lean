prelude
import Init.Prelude
import Init.Notation
import Init.Core

namespace L4L

universe u v

axiom prfIrrelEq {P : Prop} (p q : P) : Eq p q
axiom prfIrrel {P : Prop} (p q : P) : HEq p q
axiom prfIrrelHEq {P Q : Prop} (heq : HEq P Q) (p : P) (q : Q) : HEq p q

-- theorem forallEq' {A : Sort u} {U V : A → Sort v}
--   (hUV : (a : A) → Eq (U a) (V a))
--   : Eq ((a : A) → U a) ((b : A) → V b) := by
--   have := (funext fun x => hUV x)
--   subst this
--   rfl
--
theorem forallEq' {A : Sort u} {U V : A → Sort v}
     (hUV : ∀ (a : A), U a = V a) : ((a : A) → U a) = ((b : A) → V b) :=
     Eq.ndrec (motive := fun {V} => (∀ (a : A), U a = V a) → ((a : A) → U a) = ((b : A) → V b))
       (fun _ => Eq.refl ((a : A) → U a)) (funext fun x => hUV x) hUV

theorem appArgEq {A : Sort u} {U : Sort v}
  (f : (a : A) → U)
  {a b : A} (hab : Eq a b)
  : Eq (f a) (f b) := by
    subst hab
    rfl

theorem appArgEq' {A : Sort u} {U : Sort v}
  (f : (a : A) → U)
  (a b : A) (hab : Eq a b)
  : Eq (f a) (f b) := by
    subst hab
    rfl

def eq_of_heq: ∀ {α : Sort u} {a a' : α}, @HEq α a α a' → @Eq α a a' := 
fun {α : Sort u} {a a' : α} (h : @HEq α a α a') =>
  let_fun this := fun (x x_1 : Sort u) (x_2 : x) (x_3 : x_1) (h₁ : @HEq x x_2 x_1 x_3) =>
    @HEq.rec x x_2
      (@fun (x_4 : Sort u) (x_5 : x_4) (x_6 : @HEq x x_2 x_4 x_5) =>
        ∀ (h : @Eq (Sort u) x x_4), @Eq x_4 (@cast x x_4 h x_2) x_5)
      (@cast (∀ (x_4 : @Eq (Sort u) x x), @Eq x (@cast x x x_4 x_2) (@cast x x x_4 x_2))
        ((fun (x_4 : Sort u) (x_5 : x_4) (x_6 : @HEq x x_2 x_4 x_5) =>
            ∀ (h : @Eq (Sort u) x x_4), @Eq x_4 (@cast x x_4 h x_2) x_5)
          x x_2 (@HEq.refl x x_2))
        (@L4L.forallEq' (@Eq (Sort u) x x)
          (fun (x_4 : @Eq (Sort u) x x) => @Eq x (@cast x x x_4 x_2) (@cast x x x_4 x_2))
          (fun (x_4 : @Eq (Sort u) x x) => @Eq x (@cast x x x_4 x_2) x_2) fun (x_4 : @Eq (Sort u) x x) =>
          @L4L.appArgEq x Prop (@Eq x (@cast x x x_4 x_2)) (@cast x x x_4 x_2) x_2
            (@L4L.appArgEq' (@Eq (Sort u) x x) x
              (@Eq.rec (Sort u) x (fun (x_5 : Sort u) (x : @Eq (Sort u) x x_5) => x_5) x_2 x) x_4 (@Eq.refl (Sort u) x)
              (@L4L.prfIrrelEq (@Eq (Sort u) x x) x_4 (@Eq.refl (Sort u) x))))
        fun (x_4 : @Eq (Sort u) x x) => @rfl x (@cast x x x_4 x_2))
      x_1 x_3 h₁;
  this α α a a' h (@rfl (Sort u) α)

-- axiom eq_of_heq {α : Sort u} {a a' : α} (h : HEq a a') : Eq a a'

def castHEq (α β : Sort u) (h : HEq α β) (a : α) : β := cast (eq_of_heq h) a

axiom castOrigHEq {α β : Sort u} : (h : HEq α β) → (a : α) → HEq (castHEq _ _ h a) a

axiom forallHEq {A : Sort u} {U V : Sort v}
  (hUV : HEq U V)
  : HEq ((a : A) → U) ((b : A) → V)

axiom forallHEq' {A : Sort u} {U V : A → Sort v}
  (hUV : (a : A) → HEq (U a) (V a))
  : HEq ((a : A) → U a) ((b : A) → V b)

axiom forallHEqAB {A B : Sort u} {U V : Sort v}
  (hAB : HEq A B) (hUV : HEq U V)
  : HEq ((a : A) → U) ((b : B) → V)

axiom forallHEqAB' {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (hAB : HEq A B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
  : HEq ((a : A) → U a) ((b : B) → V b)

axiom appArgHEq {A : Sort u} {U : Sort v}
  (f : (a : A) → U)
  {a b : A} (hab : HEq a b)
  : HEq (f a) (f b)

axiom appArgHEq' {A : Sort u} {U : A → Sort v}
  (f : (a : A) → U a)
  (a b : A) (hab : HEq a b)
  : HEq (f a) (f b)

axiom appFunHEq {A : Sort u} {U : Sort v}
  {f g : (a : A) → U} (a : A)
  (hfg : HEq f g)
  : HEq (f a) (g a)

axiom appFunHEq' {A : Sort u} {U : A → Sort v}
  {f g : (a : A) → U a} (a : A)
  (hfg : HEq f g)
  : HEq (f a) (g a)

axiom appHEq {A : Sort u} {U : Sort v}
  {f g : (a : A) → U} {a b : A}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b)

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

axiom lambdaHEq' {A : Sort u} {U : A → Sort v}
  (f g : (a : A) → U a)
  (hfg : (a : A) → HEq (f a) (g a))
  : HEq (fun a => f a) (fun b => g b)

axiom lambdaHEqUV {A : Sort u} {U V : Sort v}
  (f : (a : A) → U) (g : (b : A) → V)
  (hfg : (a : A) → HEq (f a) (g a))
  : HEq (fun a => f a) (fun b => g b)

axiom lambdaHEqUV' (A : Sort u) (U V : A → Sort v)
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
