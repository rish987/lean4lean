theorem appArgHEq {A : Sort u} {U : A → Sort v}
  {f : (a : A) → U a} {a b : A} (hab : HEq a b)
  : HEq (f a) (f b) := by
  subst hab
  rfl

theorem appHEq {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (hAB : A = B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
  {f : (a : A) → U a} {g : (b : B) → V b} {a : A} {b : B}
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b) := by
  subst hAB
  have : U = V := by
    apply funext
    intro x
    exact eq_of_heq (hUV x x HEq.rfl)
  subst this
  subst hab
  subst hfg
  rfl

theorem appHEqBinNatFn {T : Type}
  {f : Nat → Nat → T} {a1 a2 : Nat} {b1 b2 : Nat}
  (ha : HEq a1 a2)
  (hb : HEq b1 b2)
  : HEq (f a1 b1) (f a2 b2) := by
  subst ha
  subst hb
  rfl

theorem lambdaHEq {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (f : (a : A) → U a) (g : (b : B) → V b)
  (hAB : A = B) (hfg : (a : A) → (b : B) → HEq a b → HEq (f a) (g b))
  : HEq (fun a => f a) (fun b => g b) := by
  subst hAB
  have hUV : U = V := by
    apply funext
    intro x
    exact type_eq_of_heq (hfg x x HEq.rfl)
  subst hUV
  have : f = g := funext fun a => eq_of_heq $ hfg a a HEq.rfl
  exact heq_of_eq this

theorem forAllHEq {A B : Sort u} {U : A → Sort v} {V : B → Sort v}
  (hAB : A = B) (hUV : (a : A) → (b : B) → HEq a b → HEq (U a) (V b))
  : ((a : A) → U a) = ((b : B) → V b) := by
  subst hAB
  have : U = V := by
    apply funext
    intro x
    exact eq_of_heq $ hUV x x HEq.rfl
  subst this
  rfl
