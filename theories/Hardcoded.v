Require Import Coquedille.Ast.
Require Import List.
Import ListNotations.
Require Import String.

Local Open Scope string_scope.

Definition eq_elim_term (eq: Ced.Term) (eqty : Ced.Typ) (y: Ced.Term): Ced.Term :=
  Ced.TMu None eq
          (Some
             (Ced.TyLam
                (Ced.Named "x")
                (Some eqty)
                (Ced.TyLam
                   Ced.Anon
                   (Some (Ced.TyApp
                      (Ced.TyVar "eq")
                      [(false, inl eqty);
                         (false, inr y);
                         (false, inr (Ced.TVar "x"))]))
                   (Ced.TyEq y (Ced.TVar "x")))
             )
          )
          [(Ced.TVar "eq_refl", Ced.TBeta)].

Definition False_term :=
  Ced.AssgnType "False"
                (Some Ced.KdStar)
                (Ced.TyAll (Ced.Named "X")
                           Ced.KdStar
                           (Ced.TyVar "X")).

Definition False_ind_term : Ced.Assgn :=
  Ced.AssgnTerm "False_ind"
                (Some (Ced.TyAll
                         (Ced.Named "P")
                         Ced.KdStar
                         (Ced.TyPi Ced.Anon (Ced.TyVar "False")
                                   (Ced.TyVar "P"))))
                (Ced.TLamK (Ced.Named "P")
                           (Some Ced.KdStar)
                           (Ced.TLam (Ced.Named "f")
                                     false
                                     (Some (Ced.TyVar "False"))
                                     (Ced.TApp (Ced.TVar "f")
                                               [(false, inl (Ced.TyVar "P"))]))).

Definition JMeq_rect_term : Ced.Assgn :=
  (Ced.AssgnTerm "JMeq_rect"
                 (Some
                    (Ced.TyAll (Ced.Named "A") Ced.KdStar
                               (Ced.TyPi (Ced.Named "x")
                                         (Ced.TyVar "A")
                                         (Ced.TyAll (Ced.Named "P")
                                                    (Ced.KdAll Ced.Anon
                                                               (inr (Ced.TyVar "A"))
                                                               Ced.KdStar)
                                                    (Ced.TyPi Ced.Anon
                                                              (Ced.TyApp
                                                                 (Ced.TyVar "P")
                                                                 [(false, inl (Ced.TyVar "x"))])
                                                              (Ced.TyPi
                                                                 (Ced.Named "y")
                                                                 (Ced.TyVar "A")
                                                                 (Ced.TyPi
                                                                    (Ced.Anon)
                                                                    (Ced.TyApp
                                                                       (Ced.TyVar "JMeq")
                                                                       [
                                                                         (false, inl (Ced.TyVar "A"));
                                                                         (false, inl (Ced.TyVar "x"));
                                                                         (false, inl (Ced.TyVar "A"));
                                                                         (false, inl (Ced.TyVar "y"))])
                                                                    (Ced.TyApp
                                                                       (Ced.TyVar "P")
                                                                       [(false, inl (Ced.TyVar "y"))]
                                                                    )
                 )))))))
                 (Ced.TLamK (Ced.Named "A") (Some Ced.KdStar)
                            (Ced.TLam (Ced.Named "x") false
                                      (Some (Ced.TyVar "A"))
                                      (Ced.TLamK (Ced.Named "P")
                                                 (Some (Ced.KdAll Ced.Anon
                                                            (inr (Ced.TyVar "A")) Ced.KdStar))
                                                 (Ced.TLam (Ced.Named "p") false
                                                           (Some (Ced.TyApp (Ced.TyVar "P")
                                                                      [(false, inl (Ced.TyVar "x"))]))
                                                           (Ced.TLam (Ced.Named "y") false
                                                                     (Some (Ced.TyVar "A"))
                                                                     (Ced.TLam
                                                                        (Ced.Named "H") false
                                                                        (Some (Ced.TyApp
                                                                           (Ced.TyVar "JMeq")
                                                                           [(false, inl (Ced.TyVar "A"));
                                                                              (false, inl (Ced.TyVar "x"));
                                                                              (false, inl (Ced.TyVar "A"));
                                                                              (false, inl (Ced.TyVar "y"))]))
                                                                        (Ced.TMu
                                                                           None
                                                                           (Ced.TVar "H")
                                                                           (Some (Ced.TyLamK
                                                                                    (Ced.Named "A1")
                                                                                    (Some Ced.KdStar)
                                                                                    (Ced.TyLam
                                                                                       (Ced.Named "y1")
                                                                                       (Some (Ced.TyVar "A1"))
                                                                                       (Ced.TyLam
                                                                                          Ced.Anon
                                                                                          (Some (Ced.TyApp
                                                                                             (Ced.TyVar "JMeq")
                                                                                             [(false, inl (Ced.TyVar "A"));
                                                                                              (false, inl (Ced.TyVar "x"));
                                                                                              (false, inl (Ced.TyVar "A1"));
                                                                                              (false, inl (Ced.TyVar "y1"))
                                                                                          ]))
                                                                                          (Ced.TyApp
                                                                                             (Ced.TyVar "P")
                                                                                             [(false, inl (Ced.TyVar "y"))])
                                                                           ))))
                                                                           [(Ced.TVar "JMeq_refl",
                                                                             Ced.TLetTm
                                                                               (Ced.Named "H")
                                                                               false
                                                                               (Ced.TyEq
                                                                                  (Ced.TVar "y")
                                                                                  (Ced.TVar "x"))
                                                                               (Ced.TMu
                                                                                  None
                                                                                  (Ced.TVar "H")
                                                                                  None
                                                                                  [(Ced.TVar "JMeq_refl",
                                                                                    Ced.TBeta
                                                                                  )]
                                                                               )
                                                                               (Ced.TRho
                                                                                  (Ced.TVar "H")
                                                                                  (Ced.TVar "p"))
                                                                        )])
  ))))))).

Definition appF dname vname :=
  Ced.TApp (Ced.TVar "f'")
           [(false, inr
                      (Ced.TApp (Ced.TVar ("to/" ++ dname) )
                                [(true, (inr (Ced.TVar "isType/F"))) ;
                                 (false, (inr (Ced.TVar vname)))]));
            (false,
             inr
               (Ced.TApp (Ced.TVar "F")
                         [(false, inr (Ced.TVar "n'"))]))].

Definition nat_ind_term :=
           (Ced.AssgnTerm "nat_ind"
              (Some
                 (Ced.TyAll (Ced.Named "P")
                    (Ced.KdAll (Ced.Named "n")
                       (inr (Ced.TyVar "nat")) Ced.KdStar)
                    (Ced.TyPi (Ced.Named "f")
                       (Ced.TyApp (Ced.TyVar "P")
                          [(false, inr (Ced.TVar "O"))])
                       (Ced.TyPi (Ced.Named "f'")
                          (Ced.TyPi (Ced.Named "n")
                             (Ced.TyVar "nat")
                             (Ced.TyPi Ced.Anon
                                (Ced.TyApp (Ced.TyVar "P")
                                   [(false, inr (Ced.TVar "n"))])
                                (Ced.TyApp (Ced.TyVar "P")
                                   [(false,
                                    inr
                                      (Ced.TApp
                                         (Ced.TVar "S")
                                         [(false,
                                          inr (Ced.TVar "n"))]))])))
                          (Ced.TyPi (Ced.Named "n")
                             (Ced.TyVar "nat")
                             (Ced.TyApp (Ced.TyVar "P")
                                [(false, inr (Ced.TVar "n"))]))))))
              (Ced.TLamK (Ced.Named "P")
                 (Some
                    (Ced.KdAll (Ced.Named "n")
                       (inr (Ced.TyVar "nat")) Ced.KdStar))
                 (Ced.TLam (Ced.Named "f") false
                    (Some
                       (Ced.TyApp (Ced.TyVar "P")
                          [(false, inr (Ced.TVar "O"))]))
                    (Ced.TLam (Ced.Named "f'") false
                       (Some
                          (Ced.TyPi (Ced.Named "n")
                             (Ced.TyVar "nat")
                             (Ced.TyPi Ced.Anon
                                (Ced.TyApp (Ced.TyVar "P")
                                   [(false, inr (Ced.TVar "n"))])
                                (Ced.TyApp (Ced.TyVar "P")
                                   [(false,
                                    inr
                                      (Ced.TApp
                                         (Ced.TVar "S")
                                         [(false,
                                          inr (Ced.TVar "n"))]))]))))
                       (Ced.TLam (Ced.Named "n") false
                          (Some (Ced.TyVar "nat"))
                          (Ced.TMu (Some "F")
                             (Ced.TVar "n")
                             (Some
                                (Ced.TyLam (Ced.Named "n")
                                   (Some (Ced.TyVar "nat"))
                                   (Ced.TyApp
                                      (Ced.TyVar "P")
                                      [(false, inr (Ced.TVar "n"))])))
                             [(Ced.TVar "O", Ced.TVar "f");
                             (Ced.TApp (Ced.TVar "S")
                                [(false, inl (Ced.TyVar "n'"))],
                              appF "nat" "n'")])))))).

Definition nat_rect_term :=
           (Ced.AssgnTerm "nat_rect"
              (Some
                 (Ced.TyAll (Ced.Named "P")
                    (Ced.KdAll (Ced.Named "n")
                       (inr (Ced.TyVar "nat")) Ced.KdStar)
                    (Ced.TyPi (Ced.Named "f")
                       (Ced.TyApp (Ced.TyVar "P")
                          [(false, inr (Ced.TVar "O"))])
                       (Ced.TyPi (Ced.Named "f'")
                          (Ced.TyPi (Ced.Named "n")
                             (Ced.TyVar "nat")
                             (Ced.TyPi Ced.Anon
                                (Ced.TyApp (Ced.TyVar "P")
                                   [(false, inr (Ced.TVar "n"))])
                                (Ced.TyApp (Ced.TyVar "P")
                                   [(false,
                                    inr
                                      (Ced.TApp
                                         (Ced.TVar "S")
                                         [(false,
                                          inr (Ced.TVar "n"))]))])))
                          (Ced.TyPi (Ced.Named "n")
                             (Ced.TyVar "nat")
                             (Ced.TyApp (Ced.TyVar "P")
                                [(false, inr (Ced.TVar "n"))]))))))
              (Ced.TLamK (Ced.Named "P")
                 (Some
                    (Ced.KdAll (Ced.Named "n")
                       (inr (Ced.TyVar "nat")) Ced.KdStar))
                 (Ced.TLam (Ced.Named "f") false
                    (Some
                       (Ced.TyApp (Ced.TyVar "P")
                          [(false, inr (Ced.TVar "O"))]))
                    (Ced.TLam (Ced.Named "f'") false
                       (Some
                          (Ced.TyPi (Ced.Named "n")
                             (Ced.TyVar "nat")
                             (Ced.TyPi Ced.Anon
                                (Ced.TyApp (Ced.TyVar "P")
                                   [(false, inr (Ced.TVar "n"))])
                                (Ced.TyApp (Ced.TyVar "P")
                                   [(false,
                                    inr
                                      (Ced.TApp
                                         (Ced.TVar "S")
                                         [(false,
                                          inr (Ced.TVar "n"))]))]))))
                       (Ced.TLam (Ced.Named "n") false
                          (Some (Ced.TyVar "nat"))
                          (Ced.TMu (Some "F")
                             (Ced.TVar "n")
                             (Some
                                (Ced.TyLam (Ced.Named "n")
                                   (Some (Ced.TyVar "nat"))
                                   (Ced.TyApp
                                      (Ced.TyVar "P")
                                      [(false, inr (Ced.TVar "n"))])))
                             [(Ced.TVar "O", Ced.TVar "f");
                             (Ced.TApp (Ced.TVar "S")
                                [(false, inl (Ced.TyVar "n'"))],
                              appF "nat" "n'")])))))).


Definition list_ind_term :=
  (Ced.AssgnTerm "list_ind"
              (Some
                 (Ced.TyAll (Ced.Named "A") Ced.KdStar
                    (Ced.TyAll (Ced.Named "P")
                       (Ced.KdAll (Ced.Named "l")
                          (inr
                             (Ced.TyApp (Ced.TyVar "list")
                                [(false, inr (Ced.TVar "A"))]))
                          Ced.KdStar)
                       (Ced.TyPi (Ced.Named "f")
                          (Ced.TyApp (Ced.TyVar "P")
                             [(false,
                              inr
                                (Ced.TApp (Ced.TVar "nil")
                                   [(false, inr (Ced.TVar "A"))]))])
                          (Ced.TyPi (Ced.Named "f'")
                             (Ced.TyPi (Ced.Named "a")
                                (Ced.TyVar "A")
                                (Ced.TyPi (Ced.Named "l")
                                   (Ced.TyApp
                                      (Ced.TyVar "list")
                                      [(false, inr (Ced.TVar "A"))])
                                   (Ced.TyPi Ced.Anon
                                      (Ced.TyApp
                                         (Ced.TyVar "P")
                                         [(false,
                                          inr (Ced.TVar "l"))])
                                      (Ced.TyApp
                                         (Ced.TyVar "P")
                                         [(false,
                                          inr
                                           (Ced.TApp
                                           (Ced.TVar "cons")
                                           [
                                           (false,
                                           inr (Ced.TVar "A"));
                                           (false,
                                           inr (Ced.TVar "a"));
                                           (false,
                                           inr (Ced.TVar "l"))]))]))))
                             (Ced.TyPi (Ced.Named "l")
                                (Ced.TyApp (Ced.TyVar "list")
                                   [(false, inr (Ced.TVar "A"))])
                                (Ced.TyApp (Ced.TyVar "P")
                                   [(false, inr (Ced.TVar "l"))])))))))
              (Ced.TLamK (Ced.Named "A") (Some Ced.KdStar)
                 (Ced.TLamK (Ced.Named "P")
                    (Some
                       (Ced.KdAll (Ced.Named "l")
                          (inr
                             (Ced.TyApp (Ced.TyVar "list")
                                [(false, inr (Ced.TVar "A"))]))
                          Ced.KdStar))
                    (Ced.TLam (Ced.Named "f") false
                       (Some
                          (Ced.TyApp (Ced.TyVar "P")
                             [(false,
                              inr
                                (Ced.TApp (Ced.TVar "nil")
                                   [(false, inr (Ced.TVar "A"))]))]))
                       (Ced.TLam (Ced.Named "f'") false
                          (Some
                             (Ced.TyPi (Ced.Named "a")
                                (Ced.TyVar "A")
                                (Ced.TyPi (Ced.Named "l")
                                   (Ced.TyApp
                                      (Ced.TyVar "list")
                                      [(false, inr (Ced.TVar "A"))])
                                   (Ced.TyPi Ced.Anon
                                      (Ced.TyApp
                                         (Ced.TyVar "P")
                                         [(false,
                                          inr (Ced.TVar "l"))])
                                      (Ced.TyApp
                                         (Ced.TyVar "P")
                                         [(false,
                                          inr
                                           (Ced.TApp
                                           (Ced.TVar "cons")
                                           [
                                           (false,
                                           inr (Ced.TVar "A"));
                                           (false,
                                           inr (Ced.TVar "a"));
                                           (false,
                                           inr (Ced.TVar "l"))]))])))))
                          (Ced.TLam (Ced.Named "l") false
                             (Some
                                (Ced.TyApp (Ced.TyVar "list")
                                   [(false, inr (Ced.TVar "A"))]))
                             (Ced.TMu (Some "F")
                                (Ced.TVar "l")
                                (Some
                                   (Ced.TyLam
                                      (Ced.Named "l")
                                      (Some
                                         (Ced.TyApp
                                           (Ced.TyVar "list")
                                           [(false,
                                           inr (Ced.TVar "A"))]))
                                      (Ced.TyApp
                                         (Ced.TyVar "P")
                                         [(false,
                                          inr (Ced.TVar "l"))])))
                                [(Ced.TVar "nil", Ced.TVar "f");
                                (Ced.TApp (Ced.TVar "cons")
                                   [(false, inr (Ced.TVar "y"));
                                   (false, inl (Ced.TyVar "l'"))],
                                Ced.TApp (Ced.TVar "f'")
                                  [(false, inr (Ced.TVar "y"));
                                   (false, inr
                                             (Ced.TApp (Ced.TVar "to/list")
                                                       [(true, (inr (Ced.TVar "isType/F"))) ;
                                                        (false, (inr (Ced.TVar "l'")))]));
                                   (false,
                                    inr
                                      (Ced.TApp (Ced.TVar "F")
                                                [(false, inr (Ced.TVar "l'"))]))])]))))))).
