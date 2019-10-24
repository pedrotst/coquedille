module list.
data list (A : ★) : ★ :=
  | nil : list ·A
  | cons : A ➔ (list ·A) ➔ list ·A.

_ = list.


