module zeroneqS.
data nat : ★ =
  | O : nat
  | S : nat ➔ nat.

data eq (A : ★) (x : A) : A ➔ ★ =
  | eq_refl : eq x.

eq_ind : ∀ A : ★ . Π x : A . ∀ P : A ➔ ★ . Π f : P x . Π y : A . Π e : eq ·A x y . P y = Λ A : ★ . λ x : A . Λ P : A ➔ ★ . λ f : P x . λ y : A . λ e : eq ·A x y . μ' e @(λ y' : A . λ _ : eq ·A x y' . P y') {
  | eq_refl  ➔ f 
 }.

data True : ★ =
  | I : True.

False : ★ = ∀ X : ★ . X.

False_ind : ∀ P : ★ . False ➔ P = Λ P : ★ . λ f : False . f ·P.

not : Π A : ★ . ★ = λ A : ★ . A ➔ False.

O_S : Π n : nat . not ·(eq ·nat O (S n)) = λ n : nat . λ H : eq ·nat O (S n) . δ - ( μ' H @(λ x : nat . λ _ : eq ·nat O x . { O ≃ x }) {
  | eq_refl ➔ β 
 }).


