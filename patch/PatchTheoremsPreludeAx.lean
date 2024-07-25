prelude
namespace L4L
universe u v

inductive HEq : {α : Sort u} → α → {β : Sort u} → β → Prop where
  | refl (a : α) : HEq a a

inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a

noncomputable def cast {α β : Sort u} (h : Eq α β) (a : α) : β :=
  h.rec a

axiom prfIrrelHEq (P Q : Prop) (heq : Eq P Q) (p : Q) (q : P) : HEq p q

axiom appArgHEq {A : Sort u} {U : A → Sort v}
  (f : (a : A) → U a)
  {a b : A} (hab : HEq a b)
  : HEq (f a) (f b)

axiom appHEq {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (hAB : Eq A B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
  {f : (a : A) → U a} {g : (b : B) → V b} {a : A} {b : B}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b)

axiom appHEqBinNatFn {N : Type} {T : Type}
  {f : N → N → T} {a1 a2 : N} {b1 b2 : N}
  (ha : HEq a1 a2)
  (hb : HEq b1 b2)
  : HEq (f a1 b1) (f a2 b2)

axiom lambdaHEq {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (f : (a : A) → U a) (g : (b : B) → V b)
  (hAB : Eq A B) (hfg : (a : A) → (b : B) → HEq a b → HEq (f a) (g b))
  : HEq (fun a => f a) (fun b => g b)

axiom forallHEq : ∀ {A B : Sort u} {U : A → Sort v} {V : B → Sort v},
  @Eq (Sort u) A B →
    (∀ (a : A) (b : B), @HEq A a B b → @HEq (Sort v) (U a) (Sort v) (V b)) →
      @Eq (Sort (imax u v)) ((a : A) → U a) ((b : B) → V b)
end L4L
