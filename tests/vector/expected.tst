module vector.
data nat : ★ =
  | O : nat
  | S : nat ➔ nat.

data t (A : ★) : nat ➔ ★ =
  | nil : t ·O
  | cons : Π h : A . Π n : nat . t ·n ➔ t ·(S ·n).

_ = t.


