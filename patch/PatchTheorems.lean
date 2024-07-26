prelude
import Init.Prelude
import Init.Notation
import Init.Core

namespace L4L

universe u v

theorem forallHEq {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (hAB : A = B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
  : ((a : A) → U a) = ((b : B) → V b) :=
  @Eq.ndrec (Sort u) A
    (fun {B : Sort u} =>
      ∀ {V : B → Sort v},
        (∀ (a : A) (b : B), @HEq A a B b → @HEq (Sort v) (U a) (Sort v) (V b)) →
          @Eq (Sort (imax u v)) ((a : A) → U a) ((b : B) → V b))
    (fun {V : A → Sort v} (hUV : ∀ (a b : A), @HEq A a A b → @HEq (Sort v) (U a) (Sort v) (V b)) =>
      @letFun (@Eq (A → Sort v) U V)
        (fun (_ : @Eq (A → Sort v) U V) => @Eq (Sort (imax u v)) ((a : A) → U a) ((b : A) → V b))
        (@funext A (fun (_ : A) => Sort v) U V fun (x : A) => @eq_of_heq (Sort v) (U x) (V x) (hUV x x (@HEq.rfl A x)))
        fun (this : @Eq (A → Sort v) U V) =>
        @Eq.ndrec (A → Sort v) U
          (fun {V : A → Sort v} =>
            (∀ (a b : A), @HEq A a A b → @HEq (Sort v) (U a) (Sort v) (V b)) →
              @Eq (Sort (imax u v)) ((a : A) → U a) ((b : A) → V b))
          (fun (_ : ∀ (a b : A), @HEq A a A b → @HEq (Sort v) (U a) (Sort v) (U b)) =>
            @Eq.refl (Sort (imax u v)) ((a : A) → U a))
          V this hUV)
    B hAB V hUV

axiom prfIrrelHEq (P Q : Prop) (heq : P = Q) (p : Q) (q : P) : HEq p q

theorem appArgHEq {A : Sort u} {U : A → Sort v}
  (f : (a : A) → U a)
  {a b : A} (hab : HEq a b)
  : HEq (f a) (f b) :=
  @Eq.ndrec A a (fun {b : A} => @HEq (U a) (f a) (U b) (f b)) (@HEq.rfl (U a) (f a)) b (@eq_of_heq A a b hab)

-- axiom forallHEq {A B : Sort u} {U : A → Sort v} {V : B → Sort v} (hAB : A = B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
--   : ((a : A) → U a) = ((b : B) → V b)

theorem appHEq {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (hAB : A = B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
  {f : (a : A) → U a} {g : (b : B) → V b} {a : A} {b : B}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b) :=
  @Eq.ndrec (Sort u) A
    (fun {B : Sort u} =>
      ∀ {V : B → Sort v},
        (∀ (a : A) (b : B), @HEq A a B b → @HEq (Sort v) (U a) (Sort v) (V b)) →
          ∀ {g : (b : B) → V b} {b : B},
            @HEq ((a : A) → U a) f ((b : B) → V b) g → @HEq A a B b → @HEq (U a) (f a) (V b) (g b))
    (fun {V : A → Sort v} (hUV : ∀ (a b : A), @HEq A a A b → @HEq (Sort v) (U a) (Sort v) (V b)) {g : (b : A) → V b}
        {b : A} (hfg : @HEq ((a : A) → U a) f ((b : A) → V b) g) (hab : @HEq A a A b) =>
      @letFun (@Eq (A → Sort v) U V) (fun (_ : @Eq (A → Sort v) U V) => @HEq (U a) (f a) (V b) (g b))
        (@funext A (fun (_ : A) => Sort v) U V fun (x : A) => @eq_of_heq (Sort v) (U x) (V x) (hUV x x (@HEq.rfl A x)))
        fun (this : @Eq (A → Sort v) U V) =>
        @Eq.ndrec (A → Sort v) U
          (fun {V : A → Sort v} =>
            (∀ (a b : A), @HEq A a A b → @HEq (Sort v) (U a) (Sort v) (V b)) →
              ∀ {g : (b : A) → V b}, @HEq ((a : A) → U a) f ((b : A) → V b) g → @HEq (U a) (f a) (V b) (g b))
          (fun (_ : ∀ (a b : A), @HEq A a A b → @HEq (Sort v) (U a) (Sort v) (U b)) {g : (b : A) → U b}
              (hfg : @HEq ((a : A) → U a) f ((b : A) → U b) g) =>
            @Eq.ndrec A a (fun {b : A} => @HEq (U a) (f a) (U b) (g b))
              (@Eq.ndrec ((a : A) → U a) f (fun {g : (b : A) → U b} => @HEq (U a) (f a) (U a) (g a))
                (@HEq.rfl (U a) (f a)) g (@eq_of_heq ((a : A) → U a) f g hfg))
              b (@eq_of_heq A a b hab))
          V this hUV g hfg)
    B hAB V hUV g b hfg hab

theorem appHEqBinNatFn {N : Type} {T : Type}
  {f : N → N → T} {a1 a2 : N} {b1 b2 : N}
  (ha : HEq a1 a2)
  (hb : HEq b1 b2)
  : HEq (f a1 b1) (f a2 b2) :=
  @Eq.ndrec N a1 (fun {a2 : N} => @HEq T (f a1 b1) T (f a2 b2))
    (@Eq.ndrec N b1 (fun {b2 : N} => @HEq T (f a1 b1) T (f a1 b2)) (@HEq.rfl T (f a1 b1)) b2
      (@eq_of_heq N b1 b2 hb))
    a2 (@eq_of_heq N a1 a2 ha)

theorem lambdaHEq {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (f : (a : A) → U a) (g : (b : B) → V b)
  (hAB : A = B) (hfg : (a : A) → (b : B) → HEq a b → HEq (f a) (g b))
  : HEq (fun a => f a) (fun b => g b) :=
  @Eq.ndrec (Sort u) A
    (fun {B : Sort u} =>
      ∀ {V : B → Sort v} (g : (b : B) → V b),
        (∀ (a : A) (b : B), @HEq A a B b → @HEq (U a) (f a) (V b) (g b)) →
          @HEq ((a : A) → U a) (fun (a : A) => f a) ((b : B) → V b) fun (b : B) => g b)
    (fun {V : A → Sort v} (g : (b : A) → V b) (hfg : ∀ (a b : A), @HEq A a A b → @HEq (U a) (f a) (V b) (g b)) =>
      @letFun (@Eq (A → Sort v) U V)
        (fun (_ : @Eq (A → Sort v) U V) =>
          @HEq ((a : A) → U a) (fun (a : A) => f a) ((b : A) → V b) fun (b : A) => g b)
        (@funext A (fun (_ : A) => Sort v) U V fun (x : A) =>
          @type_eq_of_heq (U x) (V x) (f x) (g x) (hfg x x (@HEq.rfl A x)))
        fun (hUV : @Eq (A → Sort v) U V) =>
        @Eq.ndrec (A → Sort v) U
          (fun {V : A → Sort v} =>
            ∀ (g : (b : A) → V b),
              (∀ (a b : A), @HEq A a A b → @HEq (U a) (f a) (V b) (g b)) →
                @HEq ((a : A) → U a) (fun (a : A) => f a) ((b : A) → V b) fun (b : A) => g b)
          (fun (g : (b : A) → U b) (hfg : ∀ (a b : A), @HEq A a A b → @HEq (U a) (f a) (U b) (g b)) =>
            @letFun (@Eq ((a : A) → U a) f g)
              (fun (_ : @Eq ((a : A) → U a) f g) =>
                @HEq ((a : A) → U a) (fun (a : A) => f a) ((b : A) → U b) fun (b : A) => g b)
              (@funext A (fun (x : A) => U x) f g fun (a : A) => @eq_of_heq (U a) (f a) (g a) (hfg a a (@HEq.rfl A a)))
              fun (this : @Eq ((a : A) → U a) f g) =>
              @heq_of_eq ((a : A) → U a) (fun (a : A) => f a) (fun (b : A) => g b) this)
          V hUV g hfg)
    B hAB V g hfg

end L4L
