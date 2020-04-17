module refl1.
data eq (A : ★) (x : A) : A ➔ ★ =
  | eq_refl : eq x.

data nat : ★ =
  | O : nat
  | S : nat ➔ nat.

refl1 : eq ·nat (S O) (S O) = eq_refl ·nat (S O).


