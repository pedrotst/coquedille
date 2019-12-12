module le.
data nat : ★ =
  | O : nat
  | S : nat ➔ nat.

data le (n : nat) : nat ➔ ★ =
  | le_n : le n
  | le_S : Π m : nat . le m ➔ le (S m).


