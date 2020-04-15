Require Import Ascii.
Require Import String.

Require Import MetaCoq.Template.All.
Require Import Coquedille.DenoteCoq.
Require Import Coquedille.PrettyPrinter.

Require Coq.extraction.Extraction.
Extraction Language Haskell.


(* Controlling extraction of specific types *)
Extract Inductive bool => "GHC.Base.Bool" ["GHC.Base.True" "GHC.Base.False"]. (* enumeration types *)
Extract Inductive sumbool => "GHC.Base.Bool" ["GHC.Base.True" "GHC.Base.False"]
.
(* types that require parameters on their constructors *)
(* type, [constructors], recursor *)
Extract Inductive nat => "GHC.Base.Int" ["0" "(\ x -> x Prelude.+ 1)"]
  "(\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))".

Extract Constant plus             => "(Prelude.+)".
Extract Constant mult             => "(Prelude.*)".
Extract Constant PeanoNat.Nat.eqb => "( Prelude.== )".

(* Properly extract the unicode tokens *)
Extract Constant TkStar    => "['★']".
Extract Constant TkArrow   => "['➔']".
Extract Constant TkPi      => "['Π']".
Extract Constant TkAll     => "['∀']".
Extract Constant TkTDot    => "['·']".
Extract Constant TkULam    => "['Λ']".
Extract Constant TkLam     => "['λ']".
Extract Constant TkMu      => "['μ']".
Extract Constant TkDelta   => "['δ']".
Extract Constant TkBeta    => "['β']".
Extract Constant TkEq      => "['≃']".
Extract Constant TkSigma      => "['σ']".

Extract Inductive ascii => "Prelude.Char"
  [ "(\b0 b1 b2 b3 b4 b5 b6 b7 -> Data.Char.chr ( (if b0 then Data.Bits.shiftL 1 0 else 0) Prelude.+ (if b1 then Data.Bits.shiftL 1 1 else 0) Prelude.+ (if b2 then Data.Bits.shiftL 1 2 else 0) Prelude.+ (if b3 then Data.Bits.shiftL 1 3 else 0) Prelude.+ (if b4 then Data.Bits.shiftL 1 4 else 0) Prelude.+ (if b5 then Data.Bits.shiftL 1 5 else 0) Prelude.+ (if b6 then Data.Bits.shiftL 1 6 else 0) Prelude.+ (if b7 then Data.Bits.shiftL 1 7 else 0)))" ]
  "(\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0) (Data.Bits.testBit (Data.Char.ord a) 1) (Data.Bits.testBit (Data.Char.ord a) 2) (Data.Bits.testBit (Data.Char.ord a) 3) (Data.Bits.testBit (Data.Char.ord a) 4) (Data.Bits.testBit (Data.Char.ord a) 5) (Data.Bits.testBit (Data.Char.ord a) 6) (Data.Bits.testBit (Data.Char.ord a) 7))".
Extract Inlined Constant Ascii.ascii_dec => "(Prelude.==)".
Extract Inductive string => "Prelude.String" [ "([])" "(:)" ].
Extract Inlined Constant String.string_dec => "(Prelude.==)".
Extract Inlined Constant String.eqb => "(Prelude.==)".


(* Adds Everything we will test here *)

(* Require Import THISISLIBRARY. *)
(* Quote Recursively Definition p := THISISPROGRAM. *)

(* LIBRARIES *)
Require Import Coq.Init.Logic.

(* COMMANDS *)
Quote Recursively Definition rew_ex2_syntax := rew_ex2.
Quote Recursively Definition eq_ex2_hprop_syntax := eq_ex2_hprop.
Quote Recursively Definition eq_ex2_syntax := eq_ex2.
Quote Recursively Definition eq_ex2_uncurried_syntax := eq_ex2_uncurried.
Quote Recursively Definition rew_ex_syntax := rew_ex.
Quote Recursively Definition eq_ex_hprop_syntax := eq_ex_hprop.
Quote Recursively Definition eq_ex_syntax := eq_ex.
Quote Recursively Definition eq_ex_uncurried_syntax := eq_ex_uncurried.
Quote Recursively Definition iff_stepl_syntax := iff_stepl.
Quote Recursively Definition eq_stepl_syntax := eq_stepl.
Quote Recursively Definition inhabited_covariant_syntax := inhabited_covariant.
Quote Recursively Definition exists_inhabited_syntax := exists_inhabited.
Quote Recursively Definition inhabited_ind_syntax := inhabited_ind.
Quote Recursively Definition forall_exists_coincide_unique_domain_syntax := forall_exists_coincide_unique_domain.
Quote Recursively Definition forall_exists_unique_domain_coincide_syntax := forall_exists_unique_domain_coincide.
Quote Recursively Definition unique_existence_syntax := unique_existence.
Quote Recursively Definition uniqueness_syntax := uniqueness.
Quote Recursively Definition unique_syntax := unique.
Quote Recursively Definition subrelation_syntax := subrelation.
Quote Recursively Definition rew_const_syntax := rew_const.
Quote Recursively Definition eq_trans_rew_distr_syntax := eq_trans_rew_distr.
Quote Recursively Definition eq_trans_sym_distr_syntax := eq_trans_sym_distr.
Quote Recursively Definition eq_sym_map_distr_syntax := eq_sym_map_distr.
Quote Recursively Definition eq_trans_map_distr_syntax := eq_trans_map_distr.
Quote Recursively Definition eq_refl_map_distr_syntax := eq_refl_map_distr.
Quote Recursively Definition eq_id_comm_r_syntax := eq_id_comm_r.
Quote Recursively Definition eq_id_comm_l_syntax := eq_id_comm_l.
Quote Recursively Definition eq_trans_assoc_syntax := eq_trans_assoc.
Quote Recursively Definition eq_trans_sym_inv_r_syntax := eq_trans_sym_inv_r.
Quote Recursively Definition eq_trans_sym_inv_l_syntax := eq_trans_sym_inv_l.
Quote Recursively Definition eq_sym_involutive_syntax := eq_sym_involutive.
Quote Recursively Definition eq_trans_refl_r_syntax := eq_trans_refl_r.
Quote Recursively Definition eq_trans_refl_l_syntax := eq_trans_refl_l.
Quote Recursively Definition f_equal_compose_syntax := f_equal_compose.
Quote Recursively Definition f_equal5_syntax := f_equal5.
Quote Recursively Definition f_equal4_syntax := f_equal4.
Quote Recursively Definition f_equal3_syntax := f_equal3.
Quote Recursively Definition f_equal2_syntax := f_equal2.
Quote Recursively Definition rew_opp_l_syntax := rew_opp_l.
Quote Recursively Definition rew_opp_r_syntax := rew_opp_r.
Quote Recursively Definition eq_rect_r_syntax := eq_rect_r.
Quote Recursively Definition eq_rec_r_syntax := eq_rec_r.
Quote Recursively Definition eq_ind_r_syntax := eq_ind_r.
Quote Recursively Definition not_eq_sym_syntax := not_eq_sym.
Quote Recursively Definition f_equal_syntax := f_equal.
Quote Recursively Definition eq_trans_syntax := eq_trans.
Quote Recursively Definition eq_sym_syntax := eq_sym.
Quote Recursively Definition absurd_syntax := absurd.
Quote Recursively Definition eq_rec_syntax := eq_rec.
Quote Recursively Definition eq_ind_syntax := eq_ind.
Quote Recursively Definition eq_rect_syntax := eq_rect.
Quote Recursively Definition gen_syntax := gen.
Quote Recursively Definition inst_syntax := inst.
Quote Recursively Definition all_syntax := all.
Quote Recursively Definition ex2_ind_syntax := ex2_ind.
Quote Recursively Definition ex_ind_syntax := ex_ind.
Quote Recursively Definition IF_then_else_syntax := IF_then_else.
Quote Recursively Definition iff_to_and_syntax := iff_to_and.
Quote Recursively Definition iff_and_syntax := iff_and.
Quote Recursively Definition or_assoc_syntax := or_assoc.
Quote Recursively Definition or_comm_syntax := or_comm.
Quote Recursively Definition or_cancel_r_syntax := or_cancel_r.
Quote Recursively Definition or_cancel_l_syntax := or_cancel_l.
Quote Recursively Definition and_assoc_syntax := and_assoc.
Quote Recursively Definition and_comm_syntax := and_comm.
Quote Recursively Definition and_cancel_r_syntax := and_cancel_r.
Quote Recursively Definition and_cancel_l_syntax := and_cancel_l.
Quote Recursively Definition neg_false_syntax := neg_false.
Quote Recursively Definition not_iff_compat_syntax := not_iff_compat.
Quote Recursively Definition imp_iff_compat_r_syntax := imp_iff_compat_r.
Quote Recursively Definition imp_iff_compat_l_syntax := imp_iff_compat_l.
Quote Recursively Definition or_iff_compat_r_syntax := or_iff_compat_r.
Quote Recursively Definition or_iff_compat_l_syntax := or_iff_compat_l.
Quote Recursively Definition and_iff_compat_r_syntax := and_iff_compat_r.
Quote Recursively Definition and_iff_compat_l_syntax := and_iff_compat_l.
Quote Recursively Definition iff_sym_syntax := iff_sym.
Quote Recursively Definition iff_trans_syntax := iff_trans.
Quote Recursively Definition iff_refl_syntax := iff_refl.
Quote Recursively Definition iff_syntax := iff.
Quote Recursively Definition or_ind_syntax := or_ind.
Quote Recursively Definition proj2_syntax := proj2.
Quote Recursively Definition proj1_syntax := proj1.
Quote Recursively Definition and_rec_syntax := and_rec.
Quote Recursively Definition and_ind_syntax := and_ind.
Quote Recursively Definition and_rect_syntax := and_rect.
Quote Recursively Definition not_syntax := not.
Quote Recursively Definition False_rec_syntax := False_rec.
Quote Recursively Definition False_ind_syntax := False_ind.
Quote Recursively Definition False_rect_syntax := False_rect.
Quote Recursively Definition True_rec_syntax := True_rec.
Quote Recursively Definition True_ind_syntax := True_ind.
Quote Recursively Definition True_rect_syntax := True_rect.


(* We are finally ready to extract the programs we want *)
(* EXTRACT *)
Extraction "Extracted.hs" PrettySum PrettyProgram denoteCoq
rew_ex2_syntax
eq_ex2_hprop_syntax
eq_ex2_syntax
eq_ex2_uncurried_syntax
rew_ex_syntax
eq_ex_hprop_syntax
eq_ex_syntax
eq_ex_uncurried_syntax
iff_stepl_syntax
eq_stepl_syntax
inhabited_covariant_syntax
exists_inhabited_syntax
inhabited_ind_syntax
forall_exists_coincide_unique_domain_syntax
forall_exists_unique_domain_coincide_syntax
unique_existence_syntax
uniqueness_syntax
unique_syntax
subrelation_syntax
rew_const_syntax
eq_trans_rew_distr_syntax
eq_trans_sym_distr_syntax
eq_sym_map_distr_syntax
eq_trans_map_distr_syntax
eq_refl_map_distr_syntax
eq_id_comm_r_syntax
eq_id_comm_l_syntax
eq_trans_assoc_syntax
eq_trans_sym_inv_r_syntax
eq_trans_sym_inv_l_syntax
eq_sym_involutive_syntax
eq_trans_refl_r_syntax
eq_trans_refl_l_syntax
f_equal_compose_syntax
f_equal5_syntax
f_equal4_syntax
f_equal3_syntax
f_equal2_syntax
rew_opp_l_syntax
rew_opp_r_syntax
eq_rect_r_syntax
eq_rec_r_syntax
eq_ind_r_syntax
not_eq_sym_syntax
f_equal_syntax
eq_trans_syntax
eq_sym_syntax
absurd_syntax
eq_rec_syntax
eq_ind_syntax
eq_rect_syntax
gen_syntax
inst_syntax
all_syntax
ex2_ind_syntax
ex_ind_syntax
IF_then_else_syntax
iff_to_and_syntax
iff_and_syntax
or_assoc_syntax
or_comm_syntax
or_cancel_r_syntax
or_cancel_l_syntax
and_assoc_syntax
and_comm_syntax
and_cancel_r_syntax
and_cancel_l_syntax
neg_false_syntax
not_iff_compat_syntax
imp_iff_compat_r_syntax
imp_iff_compat_l_syntax
or_iff_compat_r_syntax
or_iff_compat_l_syntax
and_iff_compat_r_syntax
and_iff_compat_l_syntax
iff_sym_syntax
iff_trans_syntax
iff_refl_syntax
iff_syntax
or_ind_syntax
proj2_syntax
proj1_syntax
and_rec_syntax
and_ind_syntax
and_rect_syntax
not_syntax
False_rec_syntax
False_ind_syntax
False_rect_syntax
True_rec_syntax
True_ind_syntax
True_rect_syntax
.

(* Extraction "main.hs" PrettySum PrettyProgram denoteCoq p. *)
