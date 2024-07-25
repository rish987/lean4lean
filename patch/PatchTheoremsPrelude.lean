prelude
namespace L4L
universe u v

inductive HEq : {α : Sort u} → α → {β : Sort u} → β → Prop where
  | refl (a : α) : HEq a a

inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a

noncomputable def Eq.ndrec {α : Sort u} {a : α} {motive : α → Sort v} (m : motive a) {b : α} (h : Eq a b) : motive b :=
  h.rec m

theorem congrArg : ∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β),
  @Eq α a₁ a₂ → @Eq β (f a₁) (f a₂) :=
fun {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) (h : @Eq α a₁ a₂) =>
  @Eq.rec α a₁ (fun (x : α) (_ : @Eq α a₁ x) => @Eq β (f a₁) (f x)) (@Eq.refl β (f a₁)) a₂ h

axiom funext : ∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x},
  (∀ (x : α), @Eq (β x) (f x) (g x)) → @Eq ((x : α) → β x) f g -- TODO use prelude def when possible

noncomputable def cast {α β : Sort u} (h : Eq α β) (a : α) : β :=
  h.rec a

variable {α β φ : Sort u} {a a' : α} {b b' : β} {c : φ}
@[irreducible] def letFun {α : Sort u} {β : α → Sort v} (v : α) (f : (x : α) → β x) : β v := f v

theorem eq_of_heq : ∀ {α : Sort u} {a a' : α}, @L4L.HEq.{u} α a α a' → @L4L.Eq.{u} α a a' :=
fun {α : Sort u} {a a' : α} (h : @L4L.HEq.{u} α a α a') =>
  @letFun.{0, 0}
    (∀ (α β : Sort u) (a : α) (b : β),
      @L4L.HEq.{u} α a β b → ∀ (h : @L4L.Eq.{u + 1} (Sort u) α β), @L4L.Eq.{u} β (@L4L.cast.{u} α β h a) b)
    (fun
        (_ :
          ∀ (α β : Sort u) (a : α) (b : β),
            @L4L.HEq.{u} α a β b → ∀ (h : @L4L.Eq.{u + 1} (Sort u) α β), @L4L.Eq.{u} β (@L4L.cast.{u} α β h a) b) =>
      @L4L.Eq.{u} α (@L4L.cast.{u} α α (@L4L.Eq.refl.{u + 1} (Sort u) α) a) a')
    (fun (x x_1 : Sort u) (x_2 : x) (x_3 : x_1) (h₁ : @L4L.HEq.{u} x x_2 x_1 x_3) =>
      @L4L.HEq.rec.{0, u} x x_2
        (@fun (x_4 : Sort u) (x_5 : x_4) (_ : @L4L.HEq.{u} x x_2 x_4 x_5) =>
          ∀ (h : @L4L.Eq.{u + 1} (Sort u) x x_4), @L4L.Eq.{u} x_4 (@L4L.cast.{u} x x_4 h x_2) x_5)
        (fun (x_4 : @L4L.Eq.{u + 1} (Sort u) x x) => @L4L.Eq.refl.{u} x (@L4L.cast.{u} x x x_4 x_2)) x_1 x_3 h₁)
    fun
      (this :
        ∀ (α β : Sort u) (a : α) (b : β),
          @L4L.HEq.{u} α a β b → ∀ (h : @L4L.Eq.{u + 1} (Sort u) α β), @L4L.Eq.{u} β (@L4L.cast.{u} α β h a) b) =>
    this α α a a' h (@L4L.Eq.refl.{u + 1} (Sort u) α)

theorem Eq.subst {α : Sort u} {motive : α → Prop} {a b : α} (h₁ : Eq a b) (h₂ : motive a) : motive b :=
  Eq.ndrec h₂ h₁

theorem heq_of_eq (h : Eq a a') : HEq a a' :=
  Eq.subst h (HEq.refl a)

theorem type_eq_of_heq (h : HEq a b) : Eq α β :=
  h.rec (Eq.refl α)

axiom prfIrrelHEq (P Q : Prop) (heq : Eq P Q) (p : Q) (q : P) : HEq p q

theorem appArgHEq {A : Sort u} {U : A → Sort v}
  (f : (a : A) → U a)
  {a b : A} (hab : HEq a b)
  : HEq (f a) (f b) :=
  @Eq.ndrec A a (fun {b : A} => @HEq (U a) (f a) (U b) (f b)) (@HEq.refl (U a) (f a)) b (@eq_of_heq A a b hab)

theorem appHEq {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (hAB : Eq A B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
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
        (@funext A (fun (_ : A) => Sort v) U V fun (x : A) => @eq_of_heq (Sort v) (U x) (V x) (hUV x x (@HEq.refl A x)))
        fun (this : @Eq (A → Sort v) U V) =>
        @Eq.ndrec (A → Sort v) U
          (fun {V : A → Sort v} =>
            (∀ (a b : A), @HEq A a A b → @HEq (Sort v) (U a) (Sort v) (V b)) →
              ∀ {g : (b : A) → V b}, @HEq ((a : A) → U a) f ((b : A) → V b) g → @HEq (U a) (f a) (V b) (g b))
          (fun (_ : ∀ (a b : A), @HEq A a A b → @HEq (Sort v) (U a) (Sort v) (U b)) {g : (b : A) → U b}
              (hfg : @HEq ((a : A) → U a) f ((b : A) → U b) g) =>
            @Eq.ndrec A a (fun {b : A} => @HEq (U a) (f a) (U b) (g b))
              (@Eq.ndrec ((a : A) → U a) f (fun {g : (b : A) → U b} => @HEq (U a) (f a) (U a) (g a))
                (@HEq.refl (U a) (f a)) g (@eq_of_heq ((a : A) → U a) f g hfg))
              b (@eq_of_heq A a b hab))
          V this hUV g hfg)
    B hAB V hUV g b hfg hab

theorem appHEqBinNatFn {N : Type} {T : Type}
  {f : N → N → T} {a1 a2 : N} {b1 b2 : N}
  (ha : HEq a1 a2)
  (hb : HEq b1 b2)
  : HEq (f a1 b1) (f a2 b2) :=
  @Eq.ndrec N a1 (fun {a2 : N} => @HEq T (f a1 b1) T (f a2 b2))
    (@Eq.ndrec N b1 (fun {b2 : N} => @HEq T (f a1 b1) T (f a1 b2)) (@HEq.refl T (f a1 b1)) b2
      (@eq_of_heq N b1 b2 hb))
    a2 (@eq_of_heq N a1 a2 ha)

theorem lambdaHEq {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (f : (a : A) → U a) (g : (b : B) → V b)
  (hAB : Eq A B) (hfg : (a : A) → (b : B) → HEq a b → HEq (f a) (g b))
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
          @type_eq_of_heq (U x) (V x) (f x) (g x) (hfg x x (@HEq.refl A x)))
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
              (@funext A (fun (x : A) => U x) f g fun (a : A) => @eq_of_heq (U a) (f a) (g a) (hfg a a (@HEq.refl A a)))
              fun (this : @Eq ((a : A) → U a) f g) =>
              @heq_of_eq ((a : A) → U a) (fun (a : A) => f a) (fun (b : A) => g b) this)
          V hUV g hfg)
    B hAB V g hfg

theorem forallHEq : ∀ {A B : Sort u} {U : A → Sort v} {V : B → Sort v},
  @Eq (Sort u) A B →
    (∀ (a : A) (b : B), @HEq A a B b → @HEq (Sort v) (U a) (Sort v) (V b)) →
      @Eq (Sort (imax u v)) ((a : A) → U a) ((b : B) → V b) :=
  fun {A B : Sort u} {U : A → Sort v} {V : B → Sort v} (hAB : @Eq (Sort u) A B)
      (hUV : ∀ (a : A) (b : B), @HEq A a B b → @HEq (Sort v) (U a) (Sort v) (V b)) =>
    @Eq.ndrec (Sort u) A
      (fun {B : Sort u} =>
        ∀ {V : B → Sort v},
          (∀ (a : A) (b : B), @HEq A a B b → @HEq (Sort v) (U a) (Sort v) (V b)) →
            @Eq (Sort (imax u v)) ((a : A) → U a) ((b : B) → V b))
      (fun {V : A → Sort v} (hUV : ∀ (a b : A), @HEq A a A b → @HEq (Sort v) (U a) (Sort v) (V b)) =>
        @letFun (@Eq (A → Sort v) U V)
          (fun (_ : @Eq (A → Sort v) U V) => @Eq (Sort (imax u v)) ((a : A) → U a) ((b : A) → V b))
          (@funext A (fun (_ : A) => Sort v) U V fun (x : A) => @eq_of_heq (Sort v) (U x) (V x) (hUV x x (@HEq.refl A x)))
          fun (this : @Eq (A → Sort v) U V) =>
          @Eq.ndrec (A → Sort v) U
            (fun {V : A → Sort v} =>
              (∀ (a b : A), @HEq A a A b → @HEq (Sort v) (U a) (Sort v) (V b)) →
                @Eq (Sort (imax u v)) ((a : A) → U a) ((b : A) → V b))
            (fun (_ : ∀ (a b : A), @HEq A a A b → @HEq (Sort v) (U a) (Sort v) (U b)) =>
              @Eq.refl (Sort (imax u v)) ((a : A) → U a))
            V this hUV)
      B hAB V hUV

end L4L
