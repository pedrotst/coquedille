module lnil.
L : ★ ➔ ★ = Λ A : ★ . ∀ X : ★ . (A ➔ X ➔ X) ➔ X ➔ X.

lnil : ∀ A : ★ . L ·A = Λ A : ★ . Λ X : ★ . λ _ : A ➔ X ➔ X . λ n : X . n.


