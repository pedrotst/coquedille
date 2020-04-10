Require Import Coquedille.Ast.
Import Ced.

Require Import List.
Require Import String.
Local Open Scope string.

Require Import Coquedille.DenoteCoq.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Monads.ReaderMonad.
Require Import ExtLib.Data.Monads.WriterMonad.
Require Import ExtLib.Data.Map.FMapAList.
Import MonadNotation.

(* Token Definitions *)
Definition TkNotImpl   := "ppNotImpl".
Definition TkStar      := "★".
Definition TkArrow     := "➔".
Definition TkSpace     := " ".
Definition TkColon     := ":".
Definition TkPipe      := "|".
Definition TkDot       := ".".
Definition TkTab       := "  ".
Definition TkAnon      := "anon".
Definition TkPi        := "Π".
Definition TkAll       := "∀".
Definition TkOpenPar   := "(".
Definition TkOpenBrac  := "[".
Definition TkOpenCBrac := "{".
Definition TkCloseCBrac:= "}".
Definition TkCloseBrac := "]".
Definition TkClosePar  := ")".
Definition TkDash      := "-".
Definition TkTDot      := "·".
Definition TkData      := "data".
Definition TkLam       := "λ".
Definition TkULam      := "Λ".
Definition TkMu        := "μ".
Definition TkDelta     := "δ".
Definition TkBeta      := "β".
Definition TkRho       := "ρ".
Definition TkEq        := "≃".
Definition TkAt        := "@".
Definition TkAssgn     := "=".
Definition TkErase     := "-".
Definition TkCR        := "
".

Class Pretty (p : Type) :=
  pretty : p -> string.


Instance PrettyOption {A} {x: Pretty A}: Pretty (option A) :=
  fun o =>
    match o with
    | None => "ERR"
    | Some x => pretty x
    end.

Instance PrettySum {A} {x: Pretty A}: Pretty (string + A) :=
  fun y =>
    match y with
    | inl s =>  s
    | inr a => pretty a
    end.

Local Open Scope monad_scope.
(* Can we simplify this to a simple list and mark what lives on the kind level? *)
Definition type_ctx := alist Var (Kind + Typ).

Local Definition string_eq x y := utils.string_compare x y = Eq.

Local Instance string_RelDec : RelDec.RelDec string_eq :=
  { rel_dec := String.eqb }.

Definition alist_app {B} (a1 a2: alist string B) : alist string B :=
  @fold_alist _ _ _ (@alist_add _ _ _ _) a1 a2.

Fixpoint ppIndentation (n : nat) :=
  match n with
  | O => ""
  | S n => TkTab ++ ppIndentation n
  end.

Definition string_of_list_aux {A} (f : A -> string) (sep : string) (l : list A) (indentation: nat): string :=
  let fix aux l :=
      match l return string with
      | nil => ""
      | cons a nil => ppIndentation indentation ++ f a
      | cons a l => ppIndentation indentation ++ f a ++ sep ++ aux l
      end
  in aux l.

Definition string_of_list {A} (f : A -> string) (l : list A) (indentation: nat): string :=
  string_of_list_aux f TkCR l indentation.

Instance PrettyName : Pretty Name :=
  fun name =>
    match name with
    | Anon => TkAnon
    | Named v => v
    end.

Definition parens (b: bool) (s : string) :=
  if b then TkOpenPar ++ s ++ TkClosePar else s.


Fixpoint getVarTyp (t: Typ): option Var :=
  match t with
  | TyVar v => Some v
  | TyApp t' _ => getVarTyp t'
  | TyLam _ _ t'
  | TyLamK _ _ t'
  | TyPi _ _ t'
  | TyAll _ _ t'
  | TyAllT _ _ t' => getVarTyp t'
  | _ => None
  end.

Fixpoint getVarTerm (t: Term): option Var :=
  match t with
  | TVar v => Some v
  | TApp t' _ => getVarTerm t'
  | TLam _ _ _ t'
  | TLamK _ _ t'
  | TLetTy _ _ _ t'
  | TLetTm _ _ _ _ t' => getVarTerm t'
  | _ => None
  end.

Fixpoint getVar (t: Typ + Term): option Var :=
  match t with
  | inr t' => getVarTerm t'
  | inl t' => getVarTyp t'
  end.

Definition ppDot (b: bool) (t: Typ + Term) : state type_ctx string :=
  if b
  then ret TkErase
  else
    Γ <- get ;;
      match getVar t with
      | None => ret ""
      | Some v =>
        match alist_find _ v Γ with
        | None => ret ""
        | Some t =>
          match t with
          | inl _ => ret TkTDot
          | _ => ret ""
          end
        end
      end.

Definition appendCtx v t : state type_ctx unit :=
  Γ <- get ;;
  put (alist_add _ v t Γ).

Definition getName (x: Name) : Var :=
  match x with | Anon => "_" | Named n => n end.

Definition appSize (t: Term) :=
  match t with
  | TApp _ ts => Datatypes.length ts
  | _ => 0
  end.

Definition flattenApp (t: Typ) :=
  match t with
  | TyApp t' nil => t'
  | _ => t
  end.


Fixpoint ppKind (ki : Kind) {struct ki}: state type_ctx string :=
  match ki with
  | KdStar => ret TkStar
  | KdAll x k1 k2 =>
    k1' <- match k1 with
          | inl ki1 => ppKind ki1
          | inr ty1 => ppTyp false false ty1
          end ;;
    k2' <- ppKind k2 ;;
    match x with
    | Anon => ret (k1' ++ TkSpace ++ TkArrow ++ TkSpace ++ k2')
    | Named name => ret (TkPi ++ TkSpace ++ name ++ TkSpace
                              ++ TkColon ++ TkSpace ++ k1'
                              ++ TkSpace ++ TkDot ++ TkSpace ++ k2')
    end
  end

with ppTyp (barr bapp: bool) (t : Typ) {struct t}: state type_ctx string :=
  match t with
  | TyApp t1 ts2 =>
    t1' <- ppTyp false true t1 ;;
    let ppApp (bt: bool * (Typ + Term)) : state type_ctx string :=
        let '(b, t) := bt in
        d <- ppDot b t ;;
        match t with
        | inr t' =>
          t'' <- ppTerm false true t' ;;
          ret (d ++ t'')
        | inl t' =>
          t'' <- ppTyp false true t' ;;
          ret (d ++ t'')
        end in
    ts2' <- list_m (map ppApp ts2) ;;
    ret (parens bapp (t1' ++ TkSpace ++ string_of_list_aux id (TkSpace) ts2' 0))
  | TyPi x t1 t2 =>
    match x with
    | Anon =>
      t1' <- ppTyp true false t1 ;;
      t2' <- ppTyp false false t2 ;;
      ret (parens barr (t1' ++ TkSpace ++ TkArrow ++ TkSpace ++ t2'))
    | Named name =>
      t1' <- ppTyp false false t1 ;;
      appendCtx name (inr t1) ;;
      t2' <- ppTyp false false t2 ;;
      ret (TkPi ++ TkSpace ++ name ++ TkSpace
                ++ TkColon ++ TkSpace
                ++ t1' ++ TkSpace
                ++ TkDot ++ TkSpace ++ t2')
    end
  | TyAll x t1 t2 =>
    let name := getName x in
    k <- ppKind t1 ;;
    appendCtx name (inl t1) ;;
    t2' <- ppTyp false false t2 ;;
    ret (TkAll ++ TkSpace ++ name ++ TkSpace ++ TkColon
               ++ TkSpace ++ k ++ TkSpace ++ TkDot ++ TkSpace ++ t2')
  | TyLam x t1 t2 =>
    let name := getName x in
    t1' <- match t1 with
          | Some u => u' <- ppTyp false false u ;;
                     appendCtx name (inr u) ;;
                     ret (TkSpace ++ TkColon ++ TkSpace ++ u')
          | None =>
            appendCtx name (inr (TyVar "_")) ;;
            ret ""
          end ;;
    t2' <- ppTyp false false t2 ;;
    ret (TkLam ++ TkSpace ++ name ++ t1' ++ TkSpace ++ TkDot ++ TkSpace ++ t2')
  | TyLamK x k t2 =>
    let name := getName x in
    k' <- match k with
          | Some u => u' <- ppKind u ;;
                     appendCtx name (inl u) ;;
                     ret (TkSpace ++ TkColon ++ TkSpace ++ u')
          | None =>
            appendCtx name (inl KdStar) ;;
            ret ""
          end ;;
    t2' <- ppTyp false false t2 ;;
    ret (TkLam ++ TkSpace ++ name ++ k' ++ TkSpace ++ TkDot ++ TkSpace ++ t2')
  | TyVar v => ret v
  | TyEq t1 t2 =>
    t1' <- ppTerm false false t1 ;;
    t2' <- ppTerm false false t2 ;;
    ret (TkOpenCBrac ++ TkSpace ++ t1' ++ TkSpace ++ TkEq
                    ++ TkSpace ++ t2'
                    ++ TkSpace ++ TkCloseCBrac)
  | _ => ret "?"
  end

with ppTerm (barr bapp: bool) (t : Term) {struct t}: state type_ctx string :=
  match t with
  | TApp t1 ts2 =>
    t1' <- ppTerm false true t1 ;;
    let ppApp (bt: bool * (Typ + Term)) : state type_ctx string :=
        let '(b, t) := bt in
        d <- ppDot b t ;;
        match t with
        | inr t' =>
          t'' <- ppTerm false true t' ;;
          ret (d ++ t'')
        | inl t' =>
          t'' <- ppTyp false true t' ;;
          ret (d ++ t'')
        end in
    ts2' <- list_m (map ppApp ts2) ;;
    ret (parens bapp (t1' ++ TkSpace ++ string_of_list_aux id (TkSpace) ts2' 0))
  | TLam x b ty t =>
    let name := getName x in
    ty' <- match ty with
          | Some u => u' <- ppTyp false false u ;;
                     appendCtx name (inr u) ;;
                     ret (TkSpace ++ TkColon ++ TkSpace ++ u')
          | None =>
            appendCtx name (inr (TyVar "_")) ;;
            ret ""
          end ;;
    t' <- ppTerm false false t ;;
    let tk := if b then TkULam else TkLam in
    ret (parens bapp (tk ++ TkSpace ++ name ++ ty' ++ TkSpace
                            ++ TkDot ++ TkSpace ++ t'))
  | TVar v => ret v
  | TLamK x k t =>
    let name := getName x in
    k' <- match k with
          | Some u => u' <- ppKind u ;;
                     appendCtx name (inl u) ;;
                     ret (TkSpace ++ TkColon ++ TkSpace ++ u')
          | None =>
            appendCtx name (inl KdStar) ;;
            ret ""
          end ;;
    t' <- ppTerm false false t ;;
    ret (parens bapp (TkULam ++ TkSpace ++ name ++ k' ++ TkSpace
                            ++ TkDot ++ TkSpace ++ t'))
  | TLetTy x k ty bdy =>
    k' <- ppKind k;;
    let name := getName x in
    ty' <- ppTyp false false ty ;;
    appendCtx name (inl k) ;;
    bdy' <- ppTerm false false bdy ;;
    ret (TkOpenBrac ++ TkSpace ++ name ++ TkSpace
                    ++ TkColon ++ TkSpace ++ k' ++ TkSpace
                    ++ TkAssgn ++ TkSpace ++ ty' ++ TkSpace
                    ++ TkCloseBrac ++ TkSpace ++ TkDash
                    ++ TkSpace ++ bdy')
  | TLetTm x _ ty t bdy =>
    ty' <- ppTyp false false ty ;;
    let name := getName x in
    t' <- ppTerm false false t ;;
    appendCtx name (inr ty) ;;
    bdy' <- ppTerm false false bdy ;;
    ret (TkOpenBrac ++ TkSpace ++ name ++ TkSpace
                    ++ TkColon ++ TkSpace ++ ty' ++ TkSpace
                    ++ TkAssgn ++ TkSpace ++ t' ++ TkSpace
                    ++ TkCloseBrac ++ TkSpace ++ TkDash
                    ++ TkSpace ++ bdy')
  | TMu b t mot brchs =>
    let printBranch (brch : Term * Term) : state type_ctx string :=
        let '(t1, t2) := brch in
        t1' <- ppTerm false false t1 ;;
        t2' <- ppTerm false false t2 ;;
        ret (TkPipe ++ TkSpace ++ t1' ++ TkSpace
                    ++ TkArrow ++ TkSpace ++ t2' ++ TkSpace) in
    let printMotive (mmot : option Typ) : state type_ctx string :=
        match mmot with
        | None => ret ""
        | Some mot =>
          mot' <- ppTyp false false mot ;;
               ret (TkAt ++ TkOpenPar ++ mot' ++ TkClosePar ++ TkSpace)
        end in
    t' <- ppTerm false false t ;;
    mot' <- printMotive mot ;;
    let isrec := match b with
                 | None =>  "'"
                 | Some s => (TkSpace ++ s ++ TkDot)
                 end in
    brchs' <- list_m (map printBranch brchs) ;;
               ret (TkMu ++ isrec ++ TkSpace ++ t' ++ TkSpace ++ mot' ++ TkOpenCBrac
                         ++ TkCR ++ (string_of_list id brchs' 1)
              ++ TkCR ++ TkSpace ++ TkCloseCBrac)
  | TDelta t =>
    t' <- ppTerm false false t ;;
    ret (TkDelta ++ TkSpace ++ TkDash ++ TkSpace ++ TkOpenPar
                 ++ TkSpace ++ t' ++ TkClosePar)
  | TRho t1 t2 =>
    lhs <- ppTerm false false t1 ;;
    rhs <- ppTerm false false t2 ;;
    ret (TkRho ++ TkSpace ++ lhs ++ TkSpace ++ TkDash ++ TkSpace ++ rhs)
  | TBeta => ret TkBeta
  end.

Definition runPpKind (ki: Kind) (Γ : type_ctx) :=
  fst (runState (ppKind ki) Γ).

Definition runPpTyp (t: Typ) (Γ : type_ctx) :=
  fst (runState (ppTyp false false t) Γ).

Definition runPpTerm (t: Term) (Γ : type_ctx) :=
  fst (runState (ppTerm false false t) Γ).

Definition appendNamed (x: Name) (kty : Kind + Typ): state type_ctx unit :=
  match x with
  | Anon => ret tt
  | Named name => appendCtx name kty
  end.

Fixpoint removeBindingsTyp (t: Typ) (n: nat) : state type_ctx Typ :=
match n with
| O => ret t
| S n' =>
  match t with
  | TyPi x t1 t2 =>
    t' <- removeBindingsTyp t2 (pred n);;
    appendNamed x (inr t1) ;;
    ret t'
  | TyAll x k t2 =>
    t' <- removeBindingsTyp t2 (pred n);;
    appendNamed x (inl k) ;;
    ret t'
  | _ => ret t
  end
end.

Fixpoint removeBindingsK (k: Kind) (n: nat) : state type_ctx Kind :=
match n with
| O => ret k
| S n' =>
  match k with
  | KdAll x k1 k2 =>
    k' <- removeBindingsK k2 (pred n);;
    appendNamed x (inl k) ;;
    ret k'
  | _ => ret k
  end
end.

Fixpoint removeParams (data_name : Var) (params_count: nat) (t: Typ): Typ :=
  let removeParams' := removeParams data_name params_count in
  match t with
  | TyApp t1 ts2 =>
    match t1 with
    | TyVar v =>
      if (string_dec v data_name)
      then let rs' := skipn params_count ts2 in
           flattenApp (TyApp t1 rs')
      else flattenApp (TyApp t1 ts2)
    | _ => TyApp (removeParams' t1) ts2
    end
  | TyPi x t1 t2 => TyPi x (removeParams' t1) (removeParams' t2)
  | _ => t
end.

Definition ppctor (params_count: nat) (data_name: Var) (ctor: Ctor): state type_ctx string :=
  match ctor with
  | Ctr cname ty =>
    no_bindings_t <- (removeBindingsTyp ty params_count) ;;
    (* Apps with the constructor in cedille doesn't explicitely show the parameters *)
    let no_params_t := removeParams data_name params_count no_bindings_t in
    Γ <- get ;;
    t' <- ppTyp false false no_params_t ;;
    put Γ ;;
    ret (TkPipe ++ TkSpace ++ cname ++ TkSpace ++ TkColon ++ TkSpace ++ t')
  end.

Instance PrettyParams : Pretty Params :=
  fix pp params :=
    match params with
    | nil => ""
    | cons (n, t) ps =>
      let t' := match t with | inl k => runPpKind k nil | inr ty => runPpTyp ty nil end in
      TkSpace ++ TkOpenPar ++ n ++ TkSpace
              ++ TkColon ++ TkSpace ++ t'
              ++ TkClosePar ++ pp ps
    end.

Program Definition ppDatatype (name : Var) (params: Params) (ki : Kind) (ctors : list Ctor) : state type_ctx string :=
  noparams_kind <- removeBindingsK ki (Datatypes.length params) ;;
  ki' <- ppKind noparams_kind ;;
  ctorlist <- list_m (map (ppctor (List.length params) name) ctors) ;;
  let ctors' := string_of_list id ctorlist 1 in
  ret (TkData ++ TkSpace ++ name ++ pretty params ++ TkSpace ++ TkColon ++ TkSpace
          ++ ki' ++ TkSpace ++ TkAssgn ++ TkCR
          ++ ctors' ++ TkDot).

Definition ppmKind (v: Var) (mki : option Kind) : state type_ctx string :=
  match mki with
  | None => ret ""
  | Some ki =>
    ki' <- ppKind ki ;;
    appendCtx v (inl ki) ;;
    ret (TkColon ++ TkSpace ++ ki' ++ TkSpace)
  end.

Definition ppmType (v: Var) (mty : option Typ) : state type_ctx string :=
  match mty with
  | None => ret ""
  | Some ty =>
    ty' <- ppTyp false false ty ;;
    appendCtx v (inr ty) ;;
    ret (TkColon ++ TkSpace ++ ty' ++ TkSpace)
  end.

Program Definition ppCmd (c: Cmd): state type_ctx string :=
  Γ <- get ;;
  match c with
  | CmdAssgn (AssgnTerm v mty t) =>
    typ <- ppmType v mty ;;
    t' <- ppTerm false false t ;;
    ret (v ++ TkSpace ++ typ ++ TkAssgn
           ++ TkSpace ++ t'
           ++ TkDot ++ TkCR)
  | CmdAssgn (AssgnType v mki t) =>
    ki <- ppmKind v mki ;;
    t' <- ppTyp false false t ;;
    ret (v ++ TkSpace ++ ki ++ TkAssgn
           ++ TkSpace ++ t'
           ++ TkDot ++ TkCR)
  | CmdData (DefData name params kty ctors)  =>
    appendCtx name (inl kty) ;;
    s <- (ppDatatype name params kty ctors) ;;
    ret (s ++ TkCR)
  end.

Fixpoint ppProgram' (p : Program) : state type_ctx string :=
  match p with
  | nil => ret ""
  | c :: cs =>
    c' <- ppCmd c ;;
    cs' <- ppProgram' cs ;;
    ret (c' ++ TkCR ++ cs')
  end.

Instance PrettyProgram : Pretty Program :=
  fun p => fst (@runState _ _ (ppProgram' p) nil).

Definition showState :=
  fun p => snd (@runState _ _ (ppProgram' p) nil).
