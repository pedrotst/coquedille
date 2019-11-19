module nat.
data nat : ★ =
  | O : nat
  | S : nat ➔ nat.

_ = nat.

