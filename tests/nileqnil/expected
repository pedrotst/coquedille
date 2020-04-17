module nileqnil.
data eq (A : ★) (x : A) : A ➔ ★ =
  | eq_refl : eq x.

data list (A : ★) : ★ =
  | nil : list
  | cons : A ➔ list ➔ list.

data nat : ★ =
  | O : nat
  | S : nat ➔ nat.

nileqnil : eq ·(list ·nat) (cons ·nat (S O) (nil ·nat)) (cons ·nat (S O) (nil ·nat)) = eq_refl ·(list ·nat) (cons ·nat (S O) (nil ·nat)).


