module option.
data option (A : ★) : ★ =
  | Some : A ➔ option
  | None : option.

_ = option.

