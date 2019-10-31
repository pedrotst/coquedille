module vector.
data nat : ★ =
  | O : nat
  | S : nat ➔ nat.

data t (A : ★) : ★ =
  | nil : t ·A ·O
  | cons : Π h : A . Π n : nat . (t ·A ·n) ➔ t ·A ·(S ·n).

_ = t.


