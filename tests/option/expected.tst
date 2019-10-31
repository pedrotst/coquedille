module option.
data option (A : ★) : ★ =
  | Some : A ➔ option ·A
  | None : option ·A.

_ = option.


