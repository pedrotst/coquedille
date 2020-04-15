{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Main where

import qualified Prelude
import qualified Data.Char
import GHC.IO.Encoding
import qualified Data.Bits

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

and_rect :: (() -> () -> a1) -> a1
and_rect f =
  f __ __

and_rec :: (() -> () -> a1) -> a1
and_rec =
  and_rect

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

eq_rect_r :: a1 -> a2 -> a1 -> a2
eq_rect_r =
  eq_rect

data Unit =
   Tt

andb :: GHC.Base.Bool -> GHC.Base.Bool -> GHC.Base.Bool
andb b1 b2 =
  case b1 of {
   GHC.Base.True -> b2;
   GHC.Base.False -> GHC.Base.False}

orb :: GHC.Base.Bool -> GHC.Base.Bool -> GHC.Base.Bool
orb b1 b2 =
  case b1 of {
   GHC.Base.True -> GHC.Base.True;
   GHC.Base.False -> b2}

negb :: GHC.Base.Bool -> GHC.Base.Bool
negb b =
  case b of {
   GHC.Base.True -> GHC.Base.False;
   GHC.Base.False -> GHC.Base.True}

nat_rect :: a1 -> (GHC.Base.Int -> a1 -> a1) -> GHC.Base.Int -> a1
nat_rect f f0 n =
  (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
    (\_ -> f)
    (\n0 -> f0 n0 (nat_rect f f0 n0))
    n

nat_rec :: a1 -> (GHC.Base.Int -> a1 -> a1) -> GHC.Base.Int -> a1
nat_rec =
  nat_rect

data Option a =
   Some a
 | None

option_map :: (a1 -> a2) -> (Option a1) -> Option a2
option_map f o =
  case o of {
   Some a -> Some (f a);
   None -> None}

data Sum a b =
   Inl a
 | Inr b

data Prod a b =
   Pair a b

prod_rect :: (a1 -> a2 -> a3) -> (Prod a1 a2) -> a3
prod_rect f p0 =
  case p0 of {
   Pair x x0 -> f x x0}

prod_rec :: (a1 -> a2 -> a3) -> (Prod a1 a2) -> a3
prod_rec =
  prod_rect

fst :: (Prod a1 a2) -> a1
fst p0 =
  case p0 of {
   Pair x _ -> x}

snd :: (Prod a1 a2) -> a2
snd p0 =
  case p0 of {
   Pair _ y -> y}

data List a =
   Nil
 | Cons a (List a)

list_rect :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rect f f0 l =
  case l of {
   Nil -> f;
   Cons y l0 -> f0 y l0 (list_rect f f0 l0)}

length :: (List a1) -> GHC.Base.Int
length l =
  case l of {
   Nil -> 0;
   Cons _ l' -> (\ x -> x Prelude.+ 1) (length l')}

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

data Comparison =
   Eq
 | Lt
 | Gt

id :: a1 -> a1
id x =
  x

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
data SigT a p =
   ExistT a p

proj1_sig :: a1 -> a1
proj1_sig e =
  e

projT1 :: (SigT a1 a2) -> a1
projT1 x =
  case x of {
   ExistT a _ -> a}

projT2 :: (SigT a1 a2) -> a2
projT2 x =
  case x of {
   ExistT _ h -> h}

sumbool_rect :: (() -> a1) -> (() -> a1) -> GHC.Base.Bool -> a1
sumbool_rect f f0 s =
  case s of {
   GHC.Base.True -> f __;
   GHC.Base.False -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> GHC.Base.Bool -> a1
sumbool_rec =
  sumbool_rect

pred :: GHC.Base.Int -> GHC.Base.Int
pred n =
  (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
    (\_ -> n)
    (\u -> u)
    n

sub :: GHC.Base.Int -> GHC.Base.Int -> GHC.Base.Int
sub n m =
  (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
    (\_ -> n)
    (\k ->
    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
      (\_ -> n)
      (\l -> sub k l)
      m)
    n

flip :: (a1 -> a2 -> a3) -> a2 -> a1 -> a3
flip f x y =
  f y x

eqb :: GHC.Base.Int -> GHC.Base.Int -> GHC.Base.Bool
eqb = ( Prelude.== )

eq_dec :: GHC.Base.Int -> GHC.Base.Int -> GHC.Base.Bool
eq_dec n =
  nat_rec (\m ->
    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
      (\_ -> GHC.Base.True)
      (\_ -> GHC.Base.False)
      m) (\_ iHn m ->
    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
      (\_ -> GHC.Base.False)
      (\m0 -> iHn m0)
      m) n

hd_error :: (List a1) -> Option a1
hd_error l =
  case l of {
   Nil -> None;
   Cons x _ -> Some x}

nth_error :: (List a1) -> GHC.Base.Int -> Option a1
nth_error l n =
  (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
    (\_ -> case l of {
            Nil -> None;
            Cons x _ -> Some x})
    (\n0 -> case l of {
             Nil -> None;
             Cons _ l0 -> nth_error l0 n0})
    n

rev :: (List a1) -> List a1
rev l =
  case l of {
   Nil -> Nil;
   Cons x l' -> app (rev l') (Cons x Nil)}

concat :: (List (List a1)) -> List a1
concat l =
  case l of {
   Nil -> Nil;
   Cons x l0 -> app x (concat l0)}

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f a) (map f t)}

fold_left :: (a1 -> a2 -> a1) -> (List a2) -> a1 -> a1
fold_left f l a0 =
  case l of {
   Nil -> a0;
   Cons b t -> fold_left f t (f a0 b)}

fold_right :: (a2 -> a1 -> a1) -> a1 -> (List a2) -> a1
fold_right f a0 l =
  case l of {
   Nil -> a0;
   Cons b t -> f b (fold_right f a0 t)}

filter :: (a1 -> GHC.Base.Bool) -> (List a1) -> List a1
filter f l =
  case l of {
   Nil -> Nil;
   Cons x l0 ->
    case f x of {
     GHC.Base.True -> Cons x (filter f l0);
     GHC.Base.False -> filter f l0}}

combine :: (List a1) -> (List a2) -> List (Prod a1 a2)
combine l l' =
  case l of {
   Nil -> Nil;
   Cons x tl ->
    case l' of {
     Nil -> Nil;
     Cons y tl' -> Cons (Pair x y) (combine tl tl')}}

skipn :: GHC.Base.Int -> (List a1) -> List a1
skipn n l =
  (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
    (\_ -> l)
    (\n0 -> case l of {
             Nil -> Nil;
             Cons _ l0 -> skipn n0 l0})
    n

append :: Prelude.String -> Prelude.String -> Prelude.String
append s1 s2 =
  case s1 of {
   ([]) -> s2;
   (:) c s1' -> (:) c (append s1' s2)}

length0 :: Prelude.String -> GHC.Base.Int
length0 s =
  case s of {
   ([]) -> 0;
   (:) _ s' -> (\ x -> x Prelude.+ 1) (length0 s')}

substring :: GHC.Base.Int -> GHC.Base.Int -> Prelude.String -> Prelude.String
substring n m s =
  (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
    (\_ ->
    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
      (\_ -> ([]))
      (\m' -> case s of {
               ([]) -> s;
               (:) c s' -> (:) c (substring 0 m' s')})
      m)
    (\n' -> case s of {
             ([]) -> s;
             (:) _ s' -> substring n' m s'})
    n

prefix :: Prelude.String -> Prelude.String -> GHC.Base.Bool
prefix s1 s2 =
  case s1 of {
   ([]) -> GHC.Base.True;
   (:) a s1' ->
    case s2 of {
     ([]) -> GHC.Base.False;
     (:) b s2' ->
      case (Prelude.==) a b of {
       GHC.Base.True -> prefix s1' s2';
       GHC.Base.False -> GHC.Base.False}}}

index :: GHC.Base.Int -> Prelude.String -> Prelude.String -> Option
         GHC.Base.Int
index n s1 s2 =
  case s2 of {
   ([]) ->
    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
      (\_ -> case s1 of {
              ([]) -> Some 0;
              (:) _ _ -> None})
      (\_ -> None)
      n;
   (:) _ s2' ->
    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
      (\_ ->
      case prefix s1 s2 of {
       GHC.Base.True -> Some 0;
       GHC.Base.False ->
        case index 0 s1 s2' of {
         Some n0 -> Some ((\ x -> x Prelude.+ 1) n0);
         None -> None}})
      (\n' ->
      case index n' s1 s2' of {
       Some n0 -> Some ((\ x -> x Prelude.+ 1) n0);
       None -> None})
      n}

string_of_nat :: GHC.Base.Int -> Prelude.String
string_of_nat n =
  (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
    (\_ -> (:) '0' ([]))
    (\n0 ->
    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
      (\_ -> (:) '1' ([]))
      (\n1 ->
      (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
        (\_ -> (:) '2' ([]))
        (\n2 ->
        (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
          (\_ -> (:) '3' ([]))
          (\n3 ->
          (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
            (\_ -> (:) '4' ([]))
            (\n4 ->
            (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
              (\_ -> (:) '5' ([]))
              (\n5 ->
              (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                (\_ -> (:) '6' ([]))
                (\n6 ->
                (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                  (\_ -> (:) '7' ([]))
                  (\n7 ->
                  (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                    (\_ -> (:) '8' ([]))
                    (\n8 ->
                    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                      (\_ -> (:) '9' ([]))
                      (\n9 ->
                      (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                        (\_ -> (:) '1' ((:) '0' ([])))
                        (\n10 ->
                        (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                          (\_ -> (:) '1' ((:) '1' ([])))
                          (\n11 ->
                          (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                            (\_ -> (:) '1' ((:) '2' ([])))
                            (\n12 ->
                            (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                              (\_ -> (:) '1' ((:) '3' ([])))
                              (\n13 ->
                              (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                (\_ -> (:) '1' ((:) '4' ([])))
                                (\n14 ->
                                (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                  (\_ -> (:) '1' ((:) '5' ([])))
                                  (\n15 ->
                                  (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                    (\_ -> (:) '1' ((:) '6' ([])))
                                    (\n16 ->
                                    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                      (\_ -> (:) '1' ((:) '7' ([])))
                                      (\n17 ->
                                      (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                        (\_ -> (:) '1' ((:) '8'
                                        ([])))
                                        (\n18 ->
                                        (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                          (\_ -> (:) '1' ((:) '9'
                                          ([])))
                                          (\n19 ->
                                          (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                            (\_ -> (:) '2' ((:) '0'
                                            ([])))
                                            (\n20 ->
                                            (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                              (\_ -> (:) '2' ((:) '1'
                                              ([])))
                                              (\n21 ->
                                              (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                (\_ -> (:) '2' ((:) '2'
                                                ([])))
                                                (\n22 ->
                                                (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                  (\_ -> (:) '2' ((:) '3'
                                                  ([])))
                                                  (\n23 ->
                                                  (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                    (\_ -> (:) '2' ((:) '4'
                                                    ([])))
                                                    (\n24 ->
                                                    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                      (\_ -> (:) '2' ((:) '5'
                                                      ([])))
                                                      (\n25 ->
                                                      (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                        (\_ -> (:) '2' ((:)
                                                        '6' ([])))
                                                        (\n26 ->
                                                        (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                          (\_ -> (:) '2' ((:)
                                                          '7' ([])))
                                                          (\n27 ->
                                                          (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                            (\_ -> (:) '2'
                                                            ((:) '8'
                                                            ([])))
                                                            (\n28 ->
                                                            (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                              (\_ -> (:) '2'
                                                              ((:) '9'
                                                              ([])))
                                                              (\n29 ->
                                                              (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                                (\_ -> (:)
                                                                '3' ((:) '0'
                                                                ([])))
                                                                (\n30 ->
                                                                (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                                  (\_ -> (:)
                                                                  '3' ((:)
                                                                  '1'
                                                                  ([])))
                                                                  (\n31 ->
                                                                  (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                                    (\_ ->
                                                                    (:) '3'
                                                                    ((:) '2'
                                                                    ([])))
                                                                    (\n32 ->
                                                                    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                                    (\_ ->
                                                                    (:) '3'
                                                                    ((:) '3'
                                                                    ([])))
                                                                    (\n33 ->
                                                                    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                                    (\_ ->
                                                                    (:) '3'
                                                                    ((:) '4'
                                                                    ([])))
                                                                    (\n34 ->
                                                                    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                                    (\_ ->
                                                                    (:) '3'
                                                                    ((:) '5'
                                                                    ([])))
                                                                    (\n35 ->
                                                                    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                                    (\_ ->
                                                                    (:) '3'
                                                                    ((:) '6'
                                                                    ([])))
                                                                    (\n36 ->
                                                                    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                                    (\_ ->
                                                                    (:) '3'
                                                                    ((:) '7'
                                                                    ([])))
                                                                    (\n37 ->
                                                                    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                                    (\_ ->
                                                                    (:) '3'
                                                                    ((:) '8'
                                                                    ([])))
                                                                    (\n38 ->
                                                                    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                                    (\_ ->
                                                                    (:) '3'
                                                                    ((:) '9'
                                                                    ([])))
                                                                    (\n39 ->
                                                                    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                                    (\_ ->
                                                                    (:) '4'
                                                                    ((:) '0'
                                                                    ([])))
                                                                    (\n40 ->
                                                                    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                                    (\_ ->
                                                                    (:) '4'
                                                                    ((:) '1'
                                                                    ([])))
                                                                    (\n41 ->
                                                                    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                                    (\_ ->
                                                                    (:) '4'
                                                                    ((:) '2'
                                                                    ([])))
                                                                    (\n42 ->
                                                                    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                                    (\_ ->
                                                                    (:) '4'
                                                                    ((:) '3'
                                                                    ([])))
                                                                    (\n43 ->
                                                                    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                                    (\_ ->
                                                                    (:) '4'
                                                                    ((:) '4'
                                                                    ([])))
                                                                    (\n44 ->
                                                                    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                                    (\_ ->
                                                                    (:) '4'
                                                                    ((:) '5'
                                                                    ([])))
                                                                    (\n45 ->
                                                                    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                                    (\_ ->
                                                                    (:) '4'
                                                                    ((:) '6'
                                                                    ([])))
                                                                    (\n46 ->
                                                                    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                                    (\_ ->
                                                                    (:) '4'
                                                                    ((:) '7'
                                                                    ([])))
                                                                    (\n47 ->
                                                                    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                                    (\_ ->
                                                                    (:) '4'
                                                                    ((:) '8'
                                                                    ([])))
                                                                    (\n48 ->
                                                                    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                                                                    (\_ ->
                                                                    (:) '4'
                                                                    ((:) '9'
                                                                    ([])))
                                                                    (\_ ->
                                                                    (:) 't'
                                                                    ((:) 'o'
                                                                    ((:) 'd'
                                                                    ((:) 'o'
                                                                    ((:) ' '
                                                                    ((:) 's'
                                                                    ((:) 't'
                                                                    ((:) 'r'
                                                                    ((:) 'i'
                                                                    ((:) 'n'
                                                                    ((:) 'g'
                                                                    ((:) '_'
                                                                    ((:) 'o'
                                                                    ((:) 'f'
                                                                    ((:) '_'
                                                                    ((:) 'n'
                                                                    ((:) 'a'
                                                                    ((:) 't'
                                                                    ([])))))))))))))))))))
                                                                    n48)
                                                                    n47)
                                                                    n46)
                                                                    n45)
                                                                    n44)
                                                                    n43)
                                                                    n42)
                                                                    n41)
                                                                    n40)
                                                                    n39)
                                                                    n38)
                                                                    n37)
                                                                    n36)
                                                                    n35)
                                                                    n34)
                                                                    n33)
                                                                    n32)
                                                                    n31)
                                                                  n30)
                                                                n29)
                                                              n28)
                                                            n27)
                                                          n26)
                                                        n25)
                                                      n24)
                                                    n23)
                                                  n22)
                                                n21)
                                              n20)
                                            n19)
                                          n18)
                                        n17)
                                      n16)
                                    n15)
                                  n14)
                                n13)
                              n12)
                            n11)
                          n10)
                        n9)
                      n8)
                    n7)
                  n6)
                n5)
              n4)
            n3)
          n2)
        n1)
      n0)
    n

rev0 :: (List a1) -> List a1
rev0 l =
  let {
   aux l0 acc =
     case l0 of {
      Nil -> acc;
      Cons x l1 -> aux l1 (Cons x acc)}}
  in aux l Nil

bool_compare :: GHC.Base.Bool -> GHC.Base.Bool -> Comparison
bool_compare x y =
  case x of {
   GHC.Base.True -> case y of {
                     GHC.Base.True -> Eq;
                     GHC.Base.False -> Gt};
   GHC.Base.False -> case y of {
                      GHC.Base.True -> Lt;
                      GHC.Base.False -> Eq}}

ascii_compare :: Prelude.Char -> Prelude.Char -> Comparison
ascii_compare x y =
  (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0) (Data.Bits.testBit (Data.Char.ord a) 1) (Data.Bits.testBit (Data.Char.ord a) 2) (Data.Bits.testBit (Data.Char.ord a) 3) (Data.Bits.testBit (Data.Char.ord a) 4) (Data.Bits.testBit (Data.Char.ord a) 5) (Data.Bits.testBit (Data.Char.ord a) 6) (Data.Bits.testBit (Data.Char.ord a) 7))
    (\a b c d e f g h ->
    (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0) (Data.Bits.testBit (Data.Char.ord a) 1) (Data.Bits.testBit (Data.Char.ord a) 2) (Data.Bits.testBit (Data.Char.ord a) 3) (Data.Bits.testBit (Data.Char.ord a) 4) (Data.Bits.testBit (Data.Char.ord a) 5) (Data.Bits.testBit (Data.Char.ord a) 6) (Data.Bits.testBit (Data.Char.ord a) 7))
      (\a' b' c' d' e' f' g' h' ->
      case case case case case case case bool_compare a a' of {
                                     Eq -> bool_compare b b';
                                     x0 -> x0} of {
                                Eq -> bool_compare c c';
                                x0 -> x0} of {
                           Eq -> bool_compare d d';
                           x0 -> x0} of {
                      Eq -> bool_compare e e';
                      x0 -> x0} of {
                 Eq -> bool_compare f f';
                 x0 -> x0} of {
            Eq -> bool_compare g g';
            x0 -> x0} of {
       Eq -> bool_compare h h';
       x0 -> x0})
      y)
    x

string_compare :: Prelude.String -> Prelude.String -> Comparison
string_compare x y =
  case x of {
   ([]) -> case y of {
            ([]) -> Eq;
            (:) _ _ -> Lt};
   (:) a s ->
    case y of {
     ([]) -> Gt;
     (:) b s' ->
      case ascii_compare a b of {
       Eq -> string_compare s s';
       x0 -> x0}}}

data T a =
   Sing a
 | Cons0 a (T a)

cons' :: a1 -> (List a1) -> T a1
cons' x l =
  case l of {
   Nil -> Sing x;
   Cons y l0 -> Cons0 x (cons' y l0)}

type Non_empty_list a = T a

type Ident = Prelude.String

type Kername = Prelude.String

data Name =
   NAnon
 | NNamed Ident

data Inductive =
   MkInd Kername GHC.Base.Int

inductive_mind :: Inductive -> Kername
inductive_mind i =
  case i of {
   MkInd inductive_mind0 _ -> inductive_mind0}

type Projection = Prod (Prod Inductive GHC.Base.Int) GHC.Base.Int

data Def term =
   Mkdef Name term term GHC.Base.Int

dname :: (Def a1) -> Name
dname d =
  case d of {
   Mkdef dname0 _ _ _ -> dname0}

dtype :: (Def a1) -> a1
dtype d =
  case d of {
   Mkdef _ dtype0 _ _ -> dtype0}

dbody :: (Def a1) -> a1
dbody d =
  case d of {
   Mkdef _ _ dbody0 _ -> dbody0}

rarg :: (Def a1) -> GHC.Base.Int
rarg d =
  case d of {
   Mkdef _ _ _ rarg0 -> rarg0}

type Mfixpoint term = List (Def term)

data Cast_kind =
   VmCast
 | NativeCast
 | Cast
 | RevertCast

data Recursivity_kind =
   Finite
 | CoFinite
 | BiFinite

data T0 =
   LProp
 | LSet
 | Level Prelude.String
 | Var GHC.Base.Int

t_rect :: a1 -> a1 -> (Prelude.String -> a1) -> (GHC.Base.Int -> a1) -> T0 ->
          a1
t_rect f f0 f1 f2 t =
  case t of {
   LProp -> f;
   LSet -> f0;
   Level x -> f1 x;
   Var x -> f2 x}

t_rec :: a1 -> a1 -> (Prelude.String -> a1) -> (GHC.Base.Int -> a1) -> T0 ->
         a1
t_rec =
  t_rect

eq_dec0 :: T0 -> T0 -> GHC.Base.Bool
eq_dec0 l1 l2 =
  t_rec (\x -> case x of {
                LProp -> GHC.Base.True;
                _ -> GHC.Base.False}) (\x ->
    case x of {
     LSet -> GHC.Base.True;
     _ -> GHC.Base.False}) (\s x ->
    case x of {
     Level s0 ->
      sumbool_rec (\_ -> GHC.Base.True) (\_ -> GHC.Base.False)
        ((Prelude.==) s s0);
     _ -> GHC.Base.False}) (\n x ->
    case x of {
     Var n0 ->
      sumbool_rec (\_ -> GHC.Base.True) (\_ -> GHC.Base.False) (eq_dec n n0);
     _ -> GHC.Base.False}) l1 l2

type T1 = T0

eq_dec1 :: T1 -> T1 -> GHC.Base.Bool
eq_dec1 =
  eq_dec0

type Elt = T0

type T2 = List Elt

empty :: T2
empty =
  Nil

is_empty :: T2 -> GHC.Base.Bool
is_empty l =
  case l of {
   Nil -> GHC.Base.True;
   Cons _ _ -> GHC.Base.False}

mem :: Elt -> T2 -> GHC.Base.Bool
mem x s =
  case s of {
   Nil -> GHC.Base.False;
   Cons y l ->
    case eq_dec1 x y of {
     GHC.Base.True -> GHC.Base.True;
     GHC.Base.False -> mem x l}}

add :: Elt -> T2 -> T2
add x s =
  case s of {
   Nil -> Cons x Nil;
   Cons y l ->
    case eq_dec1 x y of {
     GHC.Base.True -> s;
     GHC.Base.False -> Cons y (add x l)}}

singleton :: Elt -> T2
singleton x =
  Cons x Nil

remove :: Elt -> T2 -> T2
remove x s =
  case s of {
   Nil -> Nil;
   Cons y l ->
    case eq_dec1 x y of {
     GHC.Base.True -> l;
     GHC.Base.False -> Cons y (remove x l)}}

fold :: (Elt -> a1 -> a1) -> T2 -> a1 -> a1
fold f =
  fold_left (flip f)

union :: T2 -> T2 -> T2
union s =
  fold add s

diff :: T2 -> T2 -> T2
diff s s' =
  fold remove s' s

inter :: T2 -> T2 -> T2
inter s s' =
  fold (\x s0 ->
    case mem x s' of {
     GHC.Base.True -> add x s0;
     GHC.Base.False -> s0}) s Nil

subset :: T2 -> T2 -> GHC.Base.Bool
subset s s' =
  is_empty (diff s s')

equal :: T2 -> T2 -> GHC.Base.Bool
equal s s' =
  andb (subset s s') (subset s' s)

filter0 :: (Elt -> GHC.Base.Bool) -> T2 -> T2
filter0 f s =
  case s of {
   Nil -> Nil;
   Cons x l ->
    case f x of {
     GHC.Base.True -> Cons x (filter0 f l);
     GHC.Base.False -> filter0 f l}}

for_all :: (Elt -> GHC.Base.Bool) -> T2 -> GHC.Base.Bool
for_all f s =
  case s of {
   Nil -> GHC.Base.True;
   Cons x l ->
    case f x of {
     GHC.Base.True -> for_all f l;
     GHC.Base.False -> GHC.Base.False}}

exists_ :: (Elt -> GHC.Base.Bool) -> T2 -> GHC.Base.Bool
exists_ f s =
  case s of {
   Nil -> GHC.Base.False;
   Cons x l ->
    case f x of {
     GHC.Base.True -> GHC.Base.True;
     GHC.Base.False -> exists_ f l}}

partition :: (Elt -> GHC.Base.Bool) -> T2 -> Prod T2 T2
partition f s =
  case s of {
   Nil -> Pair Nil Nil;
   Cons x l ->
    case partition f l of {
     Pair s1 s2 ->
      case f x of {
       GHC.Base.True -> Pair (Cons x s1) s2;
       GHC.Base.False -> Pair s1 (Cons x s2)}}}

cardinal :: T2 -> GHC.Base.Int
cardinal =
  length

elements :: T2 -> List Elt
elements s =
  s

choose :: T2 -> Option Elt
choose s =
  case s of {
   Nil -> None;
   Cons x _ -> Some x}

isok :: (List Elt) -> GHC.Base.Bool
isok l =
  case l of {
   Nil -> GHC.Base.True;
   Cons a l0 -> andb (negb (mem a l0)) (isok l0)}

type T3 = T0

eq_dec2 :: T0 -> T0 -> GHC.Base.Bool
eq_dec2 =
  eq_dec1

type Elt0 = T0

type T_ = T2
  -- singleton inductive, whose constructor was Mkt
  
this :: T_ -> T2
this t =
  t

type T4 = T_

mem0 :: Elt0 -> T4 -> GHC.Base.Bool
mem0 x s =
  mem x (this s)

add0 :: Elt0 -> T4 -> T4
add0 x s =
  add x (this s)

remove0 :: Elt0 -> T4 -> T4
remove0 x s =
  remove x (this s)

singleton0 :: Elt0 -> T4
singleton0 =
  singleton

union0 :: T4 -> T4 -> T4
union0 s s' =
  union (this s) (this s')

inter0 :: T4 -> T4 -> T4
inter0 s s' =
  inter (this s) (this s')

diff0 :: T4 -> T4 -> T4
diff0 s s' =
  diff (this s) (this s')

equal0 :: T4 -> T4 -> GHC.Base.Bool
equal0 s s' =
  equal (this s) (this s')

subset0 :: T4 -> T4 -> GHC.Base.Bool
subset0 s s' =
  subset (this s) (this s')

empty0 :: T4
empty0 =
  empty

is_empty0 :: T4 -> GHC.Base.Bool
is_empty0 s =
  is_empty (this s)

elements0 :: T4 -> List Elt0
elements0 s =
  elements (this s)

choose0 :: T4 -> Option Elt0
choose0 s =
  choose (this s)

fold0 :: (Elt0 -> a1 -> a1) -> T4 -> a1 -> a1
fold0 f s =
  fold f (this s)

cardinal0 :: T4 -> GHC.Base.Int
cardinal0 s =
  cardinal (this s)

filter1 :: (Elt0 -> GHC.Base.Bool) -> T4 -> T4
filter1 f s =
  filter0 f (this s)

for_all0 :: (Elt0 -> GHC.Base.Bool) -> T4 -> GHC.Base.Bool
for_all0 f s =
  for_all f (this s)

exists_0 :: (Elt0 -> GHC.Base.Bool) -> T4 -> GHC.Base.Bool
exists_0 f s =
  exists_ f (this s)

partition0 :: (Elt0 -> GHC.Base.Bool) -> T4 -> Prod T4 T4
partition0 f s =
  let {p0 = partition f (this s)} in Pair (fst p0) (snd p0)

eq_dec3 :: T4 -> T4 -> GHC.Base.Bool
eq_dec3 s0 s'0 =
  let {b = equal s0 s'0} in
  case b of {
   GHC.Base.True -> GHC.Base.True;
   GHC.Base.False -> GHC.Base.False}

eqb0 :: T0 -> T0 -> GHC.Base.Bool
eqb0 x y =
  case eq_dec1 x y of {
   GHC.Base.True -> GHC.Base.True;
   GHC.Base.False -> GHC.Base.False}

eqb1 :: T0 -> T0 -> GHC.Base.Bool
eqb1 x y =
  case eq_dec1 x y of {
   GHC.Base.True -> GHC.Base.True;
   GHC.Base.False -> GHC.Base.False}

in_dec :: Elt0 -> T4 -> GHC.Base.Bool
in_dec x s =
  case mem0 x s of {
   GHC.Base.True -> and_rec (\_ _ -> GHC.Base.True);
   GHC.Base.False -> and_rec (\_ _ -> GHC.Base.False)}

of_list :: (List Elt0) -> T4
of_list l =
  fold_right add0 empty0 l

to_list :: T4 -> List Elt0
to_list =
  elements0

fold_rec :: (Elt0 -> a1 -> a1) -> a1 -> T4 -> (T4 -> () -> a2) -> (Elt0 -> a1
            -> T4 -> T4 -> () -> () -> () -> a2 -> a2) -> a2
fold_rec f i s pempty pstep =
  eq_rect_r (fold_right f i (rev (elements0 s)))
    (let {l = rev (elements0 s)} in
     let {pstep' = \x a s' s'' x0 -> pstep x a s' s'' __ __ __ x0} in
     list_rect (\_ _ s0 _ -> pempty s0 __) (\a l0 iHl pstep'0 _ s0 _ ->
       pstep'0 a (fold_right f i l0) (of_list l0) s0 __ __ __
         (iHl (\x a0 s' s'' _ _ _ x0 -> pstep'0 x a0 s' s'' __ __ __ x0) __
           (of_list l0) __)) l (\x a s' s'' _ _ _ x0 -> pstep' x a s' s'' x0)
       __ s __) (fold0 f s i)

fold_rec_bis :: (Elt0 -> a1 -> a1) -> a1 -> T4 -> (T4 -> T4 -> a1 -> () -> a2
                -> a2) -> a2 -> (Elt0 -> a1 -> T4 -> () -> () -> a2 -> a2) ->
                a2
fold_rec_bis f i s pmorphism pempty pstep =
  fold_rec f i s (\s' _ -> pmorphism empty0 s' i __ pempty)
    (\x a s' s'' _ _ _ x0 ->
    pmorphism (add0 x s') s'' (f x a) __ (pstep x a s' __ __ x0))

fold_rec_nodep :: (Elt0 -> a1 -> a1) -> a1 -> T4 -> a2 -> (Elt0 -> a1 -> ()
                  -> a2 -> a2) -> a2
fold_rec_nodep f i s x x0 =
  fold_rec_bis f i s (\_ _ _ _ x1 -> x1) x (\x1 a _ _ _ x2 -> x0 x1 a __ x2)

fold_rec_weak :: (Elt0 -> a1 -> a1) -> a1 -> (T4 -> T4 -> a1 -> () -> a2 ->
                 a2) -> a2 -> (Elt0 -> a1 -> T4 -> () -> a2 -> a2) -> T4 ->
                 a2
fold_rec_weak f i x x0 x1 s =
  fold_rec_bis f i s x x0 (\x2 a s' _ _ x3 -> x1 x2 a s' __ x3)

fold_rel :: (Elt0 -> a1 -> a1) -> (Elt0 -> a2 -> a2) -> a1 -> a2 -> T4 -> a3
            -> (Elt0 -> a1 -> a2 -> () -> a3 -> a3) -> a3
fold_rel f g i j s rempty rstep =
  eq_rect_r (fold_right f i (rev (elements0 s)))
    (eq_rect_r (fold_right g j (rev (elements0 s)))
      (let {l = rev (elements0 s)} in
       let {rstep' = \x a b x0 -> rstep x a b __ x0} in
       list_rect (\_ -> rempty) (\a l0 iHl rstep'0 ->
         rstep'0 a (fold_right f i l0) (fold_right g j l0) __
           (iHl (\x a0 b _ x0 -> rstep'0 x a0 b __ x0))) l (\x a b _ x0 ->
         rstep' x a b x0)) (fold0 g s j)) (fold0 f s i)

set_induction :: (T4 -> () -> a1) -> (T4 -> T4 -> a1 -> Elt0 -> () -> () ->
                 a1) -> T4 -> a1
set_induction x x0 s =
  fold_rec (\_ _ -> Tt) Tt s x (\x1 _ s' s'' _ _ _ x2 ->
    x0 s' s'' x2 x1 __ __)

set_induction_bis :: (T4 -> T4 -> () -> a1 -> a1) -> a1 -> (Elt0 -> T4 -> ()
                     -> a1 -> a1) -> T4 -> a1
set_induction_bis x x0 x1 s =
  fold_rec_bis (\_ _ -> Tt) Tt s (\s0 s' _ _ x2 -> x s0 s' __ x2) x0
    (\x2 _ s' _ _ x3 -> x1 x2 s' __ x3)

cardinal_inv_2 :: T4 -> GHC.Base.Int -> Elt0
cardinal_inv_2 s _ =
  let {l = elements0 s} in case l of {
                            Nil -> false_rect;
                            Cons e _ -> e}

cardinal_inv_2b :: T4 -> Elt0
cardinal_inv_2b s =
  let {n = cardinal0 s} in
  let {x = \x -> cardinal_inv_2 s x} in
  (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
    (\_ -> false_rect)
    (\n0 -> x n0)
    n

type Universe_level = T0

type T5 = Prod T0 GHC.Base.Bool

type T6 = Non_empty_list T5

make'' :: T5 -> (List T5) -> T6
make'' =
  cons'

type Universe = T6

data Sort_family =
   InProp
 | InSet
 | InType

data T7 =
   Lt0
 | Le
 | Eq0

t_rect0 :: a1 -> a1 -> a1 -> T7 -> a1
t_rect0 f f0 f1 t =
  case t of {
   Lt0 -> f;
   Le -> f0;
   Eq0 -> f1}

t_rec0 :: a1 -> a1 -> a1 -> T7 -> a1
t_rec0 =
  t_rect0

type Univ_constraint = Prod (Prod Universe_level T7) Universe_level

type T8 = Univ_constraint

eq_dec4 :: T8 -> T8 -> GHC.Base.Bool
eq_dec4 x y =
  prod_rec (\a b x0 ->
    case x0 of {
     Pair p0 u ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> GHC.Base.True) (\_ -> GHC.Base.False)
          (t_rec (\x1 ->
            case x1 of {
             LProp -> GHC.Base.True;
             _ -> GHC.Base.False}) (\x1 ->
            case x1 of {
             LSet -> GHC.Base.True;
             _ -> GHC.Base.False}) (\s x1 ->
            case x1 of {
             Level s0 ->
              sumbool_rec (\_ -> GHC.Base.True) (\_ -> GHC.Base.False)
                ((Prelude.==) s s0);
             _ -> GHC.Base.False}) (\n x1 ->
            case x1 of {
             Var n0 ->
              sumbool_rec (\_ -> GHC.Base.True) (\_ -> GHC.Base.False)
                (eq_dec n n0);
             _ -> GHC.Base.False}) b u)) (\_ -> GHC.Base.False)
        (prod_rec (\a0 b0 x1 ->
          case x1 of {
           Pair u0 t0 ->
            sumbool_rec (\_ ->
              sumbool_rec (\_ -> GHC.Base.True) (\_ -> GHC.Base.False)
                (t_rec0 (\x2 ->
                  case x2 of {
                   Lt0 -> GHC.Base.True;
                   _ -> GHC.Base.False}) (\x2 ->
                  case x2 of {
                   Le -> GHC.Base.True;
                   _ -> GHC.Base.False}) (\x2 ->
                  case x2 of {
                   Eq0 -> GHC.Base.True;
                   _ -> GHC.Base.False}) b0 t0)) (\_ -> GHC.Base.False)
              (eq_dec1 a0 u0)}) a p0)}) x y

type Elt1 = Univ_constraint

type T9 = List Elt1

empty1 :: T9
empty1 =
  Nil

is_empty1 :: T9 -> GHC.Base.Bool
is_empty1 l =
  case l of {
   Nil -> GHC.Base.True;
   Cons _ _ -> GHC.Base.False}

mem1 :: Elt1 -> T9 -> GHC.Base.Bool
mem1 x s =
  case s of {
   Nil -> GHC.Base.False;
   Cons y l ->
    case eq_dec4 x y of {
     GHC.Base.True -> GHC.Base.True;
     GHC.Base.False -> mem1 x l}}

add1 :: Elt1 -> T9 -> T9
add1 x s =
  case s of {
   Nil -> Cons x Nil;
   Cons y l ->
    case eq_dec4 x y of {
     GHC.Base.True -> s;
     GHC.Base.False -> Cons y (add1 x l)}}

singleton1 :: Elt1 -> T9
singleton1 x =
  Cons x Nil

remove1 :: Elt1 -> T9 -> T9
remove1 x s =
  case s of {
   Nil -> Nil;
   Cons y l ->
    case eq_dec4 x y of {
     GHC.Base.True -> l;
     GHC.Base.False -> Cons y (remove1 x l)}}

fold1 :: (Elt1 -> a1 -> a1) -> T9 -> a1 -> a1
fold1 f =
  fold_left (flip f)

union1 :: T9 -> T9 -> T9
union1 s =
  fold1 add1 s

diff1 :: T9 -> T9 -> T9
diff1 s s' =
  fold1 remove1 s' s

inter1 :: T9 -> T9 -> T9
inter1 s s' =
  fold1 (\x s0 ->
    case mem1 x s' of {
     GHC.Base.True -> add1 x s0;
     GHC.Base.False -> s0}) s Nil

subset1 :: T9 -> T9 -> GHC.Base.Bool
subset1 s s' =
  is_empty1 (diff1 s s')

equal1 :: T9 -> T9 -> GHC.Base.Bool
equal1 s s' =
  andb (subset1 s s') (subset1 s' s)

filter2 :: (Elt1 -> GHC.Base.Bool) -> T9 -> T9
filter2 f s =
  case s of {
   Nil -> Nil;
   Cons x l ->
    case f x of {
     GHC.Base.True -> Cons x (filter2 f l);
     GHC.Base.False -> filter2 f l}}

for_all1 :: (Elt1 -> GHC.Base.Bool) -> T9 -> GHC.Base.Bool
for_all1 f s =
  case s of {
   Nil -> GHC.Base.True;
   Cons x l ->
    case f x of {
     GHC.Base.True -> for_all1 f l;
     GHC.Base.False -> GHC.Base.False}}

exists_1 :: (Elt1 -> GHC.Base.Bool) -> T9 -> GHC.Base.Bool
exists_1 f s =
  case s of {
   Nil -> GHC.Base.False;
   Cons x l ->
    case f x of {
     GHC.Base.True -> GHC.Base.True;
     GHC.Base.False -> exists_1 f l}}

partition1 :: (Elt1 -> GHC.Base.Bool) -> T9 -> Prod T9 T9
partition1 f s =
  case s of {
   Nil -> Pair Nil Nil;
   Cons x l ->
    case partition1 f l of {
     Pair s1 s2 ->
      case f x of {
       GHC.Base.True -> Pair (Cons x s1) s2;
       GHC.Base.False -> Pair s1 (Cons x s2)}}}

cardinal1 :: T9 -> GHC.Base.Int
cardinal1 =
  length

elements1 :: T9 -> List Elt1
elements1 s =
  s

choose1 :: T9 -> Option Elt1
choose1 s =
  case s of {
   Nil -> None;
   Cons x _ -> Some x}

isok0 :: (List Elt1) -> GHC.Base.Bool
isok0 l =
  case l of {
   Nil -> GHC.Base.True;
   Cons a l0 -> andb (negb (mem1 a l0)) (isok0 l0)}

type T10 = Univ_constraint

eq_dec5 :: Univ_constraint -> Univ_constraint -> GHC.Base.Bool
eq_dec5 =
  eq_dec4

type Elt2 = Univ_constraint

type T_0 = T9
  -- singleton inductive, whose constructor was Mkt
  
this0 :: T_0 -> T9
this0 t =
  t

type T11 = T_0

mem2 :: Elt2 -> T11 -> GHC.Base.Bool
mem2 x s =
  mem1 x (this0 s)

add2 :: Elt2 -> T11 -> T11
add2 x s =
  add1 x (this0 s)

remove2 :: Elt2 -> T11 -> T11
remove2 x s =
  remove1 x (this0 s)

singleton2 :: Elt2 -> T11
singleton2 =
  singleton1

union2 :: T11 -> T11 -> T11
union2 s s' =
  union1 (this0 s) (this0 s')

inter2 :: T11 -> T11 -> T11
inter2 s s' =
  inter1 (this0 s) (this0 s')

diff2 :: T11 -> T11 -> T11
diff2 s s' =
  diff1 (this0 s) (this0 s')

equal2 :: T11 -> T11 -> GHC.Base.Bool
equal2 s s' =
  equal1 (this0 s) (this0 s')

subset2 :: T11 -> T11 -> GHC.Base.Bool
subset2 s s' =
  subset1 (this0 s) (this0 s')

empty2 :: T11
empty2 =
  empty1

is_empty2 :: T11 -> GHC.Base.Bool
is_empty2 s =
  is_empty1 (this0 s)

elements2 :: T11 -> List Elt2
elements2 s =
  elements1 (this0 s)

choose2 :: T11 -> Option Elt2
choose2 s =
  choose1 (this0 s)

fold2 :: (Elt2 -> a1 -> a1) -> T11 -> a1 -> a1
fold2 f s =
  fold1 f (this0 s)

cardinal2 :: T11 -> GHC.Base.Int
cardinal2 s =
  cardinal1 (this0 s)

filter3 :: (Elt2 -> GHC.Base.Bool) -> T11 -> T11
filter3 f s =
  filter2 f (this0 s)

for_all2 :: (Elt2 -> GHC.Base.Bool) -> T11 -> GHC.Base.Bool
for_all2 f s =
  for_all1 f (this0 s)

exists_2 :: (Elt2 -> GHC.Base.Bool) -> T11 -> GHC.Base.Bool
exists_2 f s =
  exists_1 f (this0 s)

partition2 :: (Elt2 -> GHC.Base.Bool) -> T11 -> Prod T11 T11
partition2 f s =
  let {p0 = partition1 f (this0 s)} in Pair (fst p0) (snd p0)

eq_dec6 :: T11 -> T11 -> GHC.Base.Bool
eq_dec6 s0 s'0 =
  let {b = equal1 s0 s'0} in
  case b of {
   GHC.Base.True -> GHC.Base.True;
   GHC.Base.False -> GHC.Base.False}

type Constraints = T11

type T12 = List T0

type Universe_instance = T12

type T13 = Prod (List Ident) Constraints

type T14 = Prod T4 Constraints

data T15 =
   Irrelevant
 | Covariant
 | Invariant

type T16 = Prod T13 (List T15)

data Universes_decl =
   Monomorphic_ctx T14
 | Polymorphic_ctx T13
 | Cumulative_ctx T16

data Term =
   TRel GHC.Base.Int
 | TVar Ident
 | TEvar GHC.Base.Int (List Term)
 | TSort Universe
 | TCast Term Cast_kind Term
 | TProd Name Term Term
 | TLambda Name Term Term
 | TLetIn Name Term Term Term
 | TApp Term (List Term)
 | TConst Kername Universe_instance
 | TInd Inductive Universe_instance
 | TConstruct Inductive GHC.Base.Int Universe_instance
 | TCase (Prod Inductive GHC.Base.Int) Term Term (List
                                                 (Prod GHC.Base.Int Term))
 | TProj Projection Term
 | TFix (Mfixpoint Term) GHC.Base.Int
 | TCoFix (Mfixpoint Term) GHC.Base.Int

data Context_decl =
   Mkdecl Name (Option Term) Term

decl_name :: Context_decl -> Name
decl_name c =
  case c of {
   Mkdecl decl_name0 _ _ -> decl_name0}

decl_type :: Context_decl -> Term
decl_type c =
  case c of {
   Mkdecl _ _ decl_type0 -> decl_type0}

type Context = List Context_decl

data One_inductive_body =
   Build_one_inductive_body Ident Term (List Sort_family) (List
                                                          (Prod
                                                          (Prod Ident Term)
                                                          GHC.Base.Int)) 
 (List (Prod Ident Term))

ind_name :: One_inductive_body -> Ident
ind_name o =
  case o of {
   Build_one_inductive_body ind_name0 _ _ _ _ -> ind_name0}

ind_type :: One_inductive_body -> Term
ind_type o =
  case o of {
   Build_one_inductive_body _ ind_type0 _ _ _ -> ind_type0}

ind_ctors :: One_inductive_body -> List (Prod (Prod Ident Term) GHC.Base.Int)
ind_ctors o =
  case o of {
   Build_one_inductive_body _ _ _ ind_ctors0 _ -> ind_ctors0}

data Mutual_inductive_body =
   Build_mutual_inductive_body Recursivity_kind GHC.Base.Int Context 
 (List One_inductive_body) Universes_decl

ind_params :: Mutual_inductive_body -> Context
ind_params m =
  case m of {
   Build_mutual_inductive_body _ _ ind_params0 _ _ -> ind_params0}

ind_bodies :: Mutual_inductive_body -> List One_inductive_body
ind_bodies m =
  case m of {
   Build_mutual_inductive_body _ _ _ ind_bodies0 _ -> ind_bodies0}

data Constant_body =
   Build_constant_body Term (Option Term) Universes_decl

cst_type :: Constant_body -> Term
cst_type c =
  case c of {
   Build_constant_body cst_type0 _ _ -> cst_type0}

cst_body :: Constant_body -> Option Term
cst_body c =
  case c of {
   Build_constant_body _ cst_body0 _ -> cst_body0}

data Global_decl =
   ConstantDecl Kername Constant_body
 | InductiveDecl Kername Mutual_inductive_body

type Global_env = List Global_decl

type Program = Prod Global_env Term

eq_nat :: GHC.Base.Int -> GHC.Base.Int -> GHC.Base.Bool
eq_nat =
  eqb

get_ident :: Name -> Prelude.String
get_ident n =
  case n of {
   NAnon -> (:) 'X' ((:) 'X' ([]));
   NNamed i -> i}

lookup_mind_decl :: Ident -> Global_env -> Option Mutual_inductive_body
lookup_mind_decl id0 decls =
  case decls of {
   Nil -> None;
   Cons g tl ->
    case g of {
     ConstantDecl _ _ -> lookup_mind_decl id0 tl;
     InductiveDecl kn d ->
      case string_compare kn id0 of {
       Eq -> Some d;
       _ -> lookup_mind_decl id0 tl}}}

type Functor f =
  () -> () -> (Any -> Any) -> f -> f
  -- singleton inductive, whose constructor was Build_Functor
  
fmap :: (Functor a1) -> (a2 -> a3) -> a1 -> a1
fmap functor x x0 =
  unsafeCoerce functor __ __ x x0

data Monad m =
   Build_Monad (() -> Any -> m) (() -> () -> m -> (Any -> m) -> m)

ret :: (Monad a1) -> a2 -> a1
ret monad x =
  case monad of {
   Build_Monad ret0 _ -> unsafeCoerce ret0 __ x}

bind :: (Monad a1) -> a1 -> (a2 -> a1) -> a1
bind monad x x0 =
  case monad of {
   Build_Monad _ bind0 -> unsafeCoerce bind0 __ __ x x0}

liftM :: (Monad a1) -> (a2 -> a3) -> a1 -> a1
liftM m f x =
  bind m x (\x0 -> ret m (f x0))

functor_Monad :: (Monad a1) -> Functor a1
functor_Monad m _ _ =
  liftM m

data MonadReader t m =
   Build_MonadReader (() -> (t -> t) -> m -> m) m

local :: (MonadReader a1 a2) -> (a1 -> a1) -> a2 -> a2
local monadReader x x0 =
  case monadReader of {
   Build_MonadReader local0 _ -> local0 __ x x0}

ask :: (MonadReader a1 a2) -> a2
ask monadReader =
  case monadReader of {
   Build_MonadReader _ ask0 -> ask0}

data MonadState t m =
   Build_MonadState m (t -> m)

get :: (MonadState a1 a2) -> a2
get monadState =
  case monadState of {
   Build_MonadState get0 _ -> get0}

put :: (MonadState a1 a2) -> a1 -> a2
put monadState =
  case monadState of {
   Build_MonadState _ put0 -> put0}

type MonadT m mt =
  () -> mt -> m
  -- singleton inductive, whose constructor was Build_MonadT
  
lift :: (MonadT a1 a2) -> a2 -> a1
lift monadT x =
  monadT __ x

data MonadExc e m =
   Build_MonadExc (() -> e -> m) (() -> m -> (e -> m) -> m)

raise :: (MonadExc a1 a2) -> a1 -> a2
raise monadExc x =
  case monadExc of {
   Build_MonadExc raise0 _ -> raise0 __ x}

catch :: (MonadExc a1 a2) -> a2 -> (a1 -> a2) -> a2
catch monadExc x x0 =
  case monadExc of {
   Build_MonadExc _ catch0 -> catch0 __ x x0}

type State s t =
  s -> Prod t s
  -- singleton inductive, whose constructor was mkState
  
runState :: (State a1 a2) -> a1 -> Prod a2 a1
runState s =
  s

monad_state :: Monad (State a1 Any)
monad_state =
  Build_Monad (\_ v s -> Pair v s) (\_ _ c1 c2 s ->
    case runState c1 s of {
     Pair v s0 -> runState (c2 v) s0})

monadState_state :: MonadState a1 (State a1 Any)
monadState_state =
  Build_MonadState (\x -> Pair (unsafeCoerce x) x) (\v _ -> Pair
    (unsafeCoerce Tt) v)

type StateT s m t =
  s -> m
  -- singleton inductive, whose constructor was mkStateT
  
runStateT :: (StateT a1 a2 a3) -> a1 -> a2
runStateT s =
  s

monad_stateT :: (Monad a2) -> Monad (StateT a1 a2 Any)
monad_stateT m =
  Build_Monad (\_ x s -> ret m (Pair x s)) (\_ _ c1 c2 s ->
    bind m (runStateT c1 s) (\vs ->
      case vs of {
       Pair v s0 -> runStateT (c2 v) s0}))

monadState_stateT :: (Monad a2) -> MonadState a1 (StateT a1 a2 Any)
monadState_stateT m =
  Build_MonadState (\x -> ret m (Pair x x)) (\v _ -> ret m (Pair Tt v))

monadT_stateT :: (Monad a2) -> MonadT (StateT a1 a2 Any) a2
monadT_stateT m _ c s =
  bind m c (\t -> ret m (Pair t s))

monadReader_stateT :: (Monad a2) -> (MonadReader a3 a2) -> MonadReader 
                      a3 (StateT a1 a2 Any)
monadReader_stateT m mR =
  Build_MonadReader (\_ f c s -> local mR f (runStateT c s)) (\s ->
    bind m (ask mR) (\t -> ret m (Pair t s)))

exc_stateT :: (Monad a2) -> (MonadExc a3 a2) -> MonadExc a3
              (StateT a1 a2 Any)
exc_stateT m mR =
  Build_MonadExc (\_ e -> lift (monadT_stateT m) (raise mR e))
    (\_ body hnd s ->
    catch mR (runStateT body s) (\e -> runStateT (hnd e) s))

type ReaderT s m t =
  s -> m
  -- singleton inductive, whose constructor was mkReaderT
  
runReaderT :: (ReaderT a1 a2 a3) -> a1 -> a2
runReaderT r =
  r

monad_readerT :: (Monad a2) -> Monad (ReaderT a1 a2 Any)
monad_readerT m =
  Build_Monad (\_ x _ -> ret m x) (\_ _ c1 c2 s ->
    bind m (runReaderT c1 s) (\v -> runReaderT (c2 v) s))

monadReader_readerT :: (Monad a2) -> MonadReader a1 (ReaderT a1 a2 Any)
monadReader_readerT m =
  Build_MonadReader (\_ f cmd x -> runReaderT cmd (f x)) (\x -> ret m x)

monadT_readerT :: MonadT (ReaderT a1 a2 Any) a2
monadT_readerT _ c _ =
  c

monadExc_readerT :: (MonadExc a3 a2) -> MonadExc a3 (ReaderT a1 a2 Any)
monadExc_readerT mE =
  Build_MonadExc (\_ v -> lift monadT_readerT (raise mE v)) (\_ c h s ->
    catch mE (runReaderT c s) (\x -> runReaderT (h x) s))

type Ident0 a = a
  -- singleton inductive, whose constructor was mkIdent
  
unIdent :: (Ident0 a1) -> a1
unIdent i =
  i

monad_ident :: Monad (Ident0 Any)
monad_ident =
  Build_Monad (\_ v -> v) (\_ _ c f -> f (unIdent c))

type EitherT t m a = m
  -- singleton inductive, whose constructor was mkEitherT
  
unEitherT :: (EitherT a1 a2 a3) -> a2
unEitherT e =
  e

monad_eitherT :: (Monad a2) -> Monad (EitherT a1 a2 Any)
monad_eitherT m =
  Build_Monad (\_ x -> ret m (Inr x)) (\_ _ c f ->
    bind m (unEitherT c) (\xM ->
      case xM of {
       Inl x -> ret m (Inl x);
       Inr x -> unEitherT (f x)}))

exception_eitherT :: (Monad a2) -> MonadExc a1 (EitherT a1 a2 Any)
exception_eitherT m =
  Build_MonadExc (\_ v -> ret m (Inl v)) (\_ c h ->
    bind m (unEitherT c) (\xM ->
      case xM of {
       Inl x -> unEitherT (h x);
       Inr x -> ret m (Inr x)}))

type RelDec t =
  t -> t -> GHC.Base.Bool
  -- singleton inductive, whose constructor was Build_RelDec
  
rel_dec :: (RelDec a1) -> a1 -> a1 -> GHC.Base.Bool
rel_dec relDec =
  relDec

type Alist k v = List (Prod k v)

alist_remove :: (RelDec a1) -> a1 -> (Alist a1 a2) -> Alist a1 a2
alist_remove rD_K k m =
  filter (\x -> negb (rel_dec rD_K k (fst x))) m

alist_add :: (RelDec a1) -> a1 -> a2 -> (Alist a1 a2) -> Alist a1 a2
alist_add rD_K k v m =
  Cons (Pair k v) (alist_remove rD_K k m)

alist_find :: (RelDec a1) -> a1 -> (Alist a1 a2) -> Option a2
alist_find rD_K k m =
  case m of {
   Nil -> None;
   Cons p0 ms ->
    case p0 of {
     Pair k' v ->
      case rel_dec rD_K k k' of {
       GHC.Base.True -> Some v;
       GHC.Base.False -> alist_find rD_K k ms}}}

type Var0 = Prelude.String

data Name0 =
   Anon
 | Named Var0

data Kind =
   KdStar
 | KdAll Name0 (Sum Kind Typ) Kind
data Typ =
   TyVar Var0
 | TyAll Name0 Kind Typ
 | TyPi Name0 Typ Typ
 | TyApp Typ (List (Prod GHC.Base.Bool (Sum Typ Term0)))
 | TyLam Name0 (Option Typ) Typ
 | TyLamK Name0 (Option Kind) Typ
 | TyAllT Name0 Typ Typ
 | TyIntersec Name0 Typ Typ
 | TyEq Term0 Term0
data Term0 =
   TVar0 Var0
 | TLam Name0 GHC.Base.Bool (Option Typ) Term0
 | TLamK Name0 (Option Kind) Term0
 | TApp0 Term0 (List (Prod GHC.Base.Bool (Sum Typ Term0)))
 | TLetTm Name0 GHC.Base.Bool Typ Term0 Term0
 | TLetTy Name0 Kind Typ Term0
 | TMu (Option Var0) Term0 (Option Typ) (List (Prod Term0 Term0))
 | TDelta Term0
 | TRho Term0 Term0
 | TBeta

data Ctor =
   Ctr Var0 Typ

type Ctors = List Ctor

type Params = List (Prod Var0 (Sum Kind Typ))

data Data =
   DefData Var0 Params Kind Ctors

data Assgn =
   AssgnTerm Var0 (Option Typ) Term0
 | AssgnType Var0 (Option Kind) Typ

data Cmd =
   CmdAssgn Assgn
 | CmdData Data

type Program0 = List Cmd

eq_elim_term :: Term0 -> Typ -> Term0 -> Term0
eq_elim_term eq eqty y =
  TMu None eq (Some (TyLam (Named ((:) 'x' ([]))) (Some eqty) (TyLam Anon
    (Some (TyApp (TyVar ((:) 'e' ((:) 'q' ([])))) (Cons (Pair GHC.Base.False
    (Inl eqty)) (Cons (Pair GHC.Base.False (Inr y)) (Cons (Pair
    GHC.Base.False (Inr (TVar0 ((:) 'x' ([]))))) Nil))))) (TyEq y (TVar0 ((:)
    'x' ([]))))))) (Cons (Pair (TVar0 ((:) 'e' ((:) 'q' ((:) '_' ((:) 'r'
    ((:) 'e' ((:) 'f' ((:) 'l' ([]))))))))) TBeta) Nil)

false_term :: Assgn
false_term =
  AssgnType ((:) 'F' ((:) 'a' ((:) 'l' ((:) 's' ((:) 'e' ([])))))) (Some
    KdStar) (TyAll (Named ((:) 'X' ([]))) KdStar (TyVar ((:) 'X' ([]))))

false_ind_term :: Assgn
false_ind_term =
  AssgnTerm ((:) 'F' ((:) 'a' ((:) 'l' ((:) 's' ((:) 'e' ((:) '_' ((:) 'i'
    ((:) 'n' ((:) 'd' ([])))))))))) (Some (TyAll (Named ((:) 'P' ([])))
    KdStar (TyPi Anon (TyVar ((:) 'F' ((:) 'a' ((:) 'l' ((:) 's' ((:) 'e'
    ([]))))))) (TyVar ((:) 'P' ([])))))) (TLamK (Named ((:) 'P' ([]))) (Some
    KdStar) (TLam (Named ((:) 'f' ([]))) GHC.Base.False (Some (TyVar ((:) 'F'
    ((:) 'a' ((:) 'l' ((:) 's' ((:) 'e' ([])))))))) (TApp0 (TVar0 ((:) 'f'
    ([]))) (Cons (Pair GHC.Base.False (Inl (TyVar ((:) 'P' ([]))))) Nil))))

jMeq_rect_term :: Assgn
jMeq_rect_term =
  AssgnTerm ((:) 'J' ((:) 'M' ((:) 'e' ((:) 'q' ((:) '_' ((:) 'r' ((:) 'e'
    ((:) 'c' ((:) 't' ([])))))))))) (Some (TyAll (Named ((:) 'A' ([])))
    KdStar (TyPi (Named ((:) 'x' ([]))) (TyVar ((:) 'A' ([]))) (TyAll (Named
    ((:) 'P' ([]))) (KdAll Anon (Inr (TyVar ((:) 'A' ([])))) KdStar) (TyPi
    Anon (TyApp (TyVar ((:) 'P' ([]))) (Cons (Pair GHC.Base.False (Inl (TyVar
    ((:) 'x' ([]))))) Nil)) (TyPi (Named ((:) 'y' ([]))) (TyVar ((:) 'A'
    ([]))) (TyPi Anon (TyApp (TyVar ((:) 'J' ((:) 'M' ((:) 'e' ((:) 'q'
    ([])))))) (Cons (Pair GHC.Base.False (Inl (TyVar ((:) 'A' ([]))))) (Cons
    (Pair GHC.Base.False (Inl (TyVar ((:) 'x' ([]))))) (Cons (Pair
    GHC.Base.False (Inl (TyVar ((:) 'A' ([]))))) (Cons (Pair GHC.Base.False
    (Inl (TyVar ((:) 'y' ([]))))) Nil))))) (TyApp (TyVar ((:) 'P' ([])))
    (Cons (Pair GHC.Base.False (Inl (TyVar ((:) 'y' ([]))))) Nil)))))))))
    (TLamK (Named ((:) 'A' ([]))) (Some KdStar) (TLam (Named ((:) 'x' ([])))
    GHC.Base.False (Some (TyVar ((:) 'A' ([])))) (TLamK (Named ((:) 'P'
    ([]))) (Some (KdAll Anon (Inr (TyVar ((:) 'A' ([])))) KdStar)) (TLam
    (Named ((:) 'p' ([]))) GHC.Base.False (Some (TyApp (TyVar ((:) 'P' ([])))
    (Cons (Pair GHC.Base.False (Inl (TyVar ((:) 'x' ([]))))) Nil))) (TLam
    (Named ((:) 'y' ([]))) GHC.Base.False (Some (TyVar ((:) 'A' ([])))) (TLam
    (Named ((:) 'H' ([]))) GHC.Base.False (Some (TyApp (TyVar ((:) 'J' ((:)
    'M' ((:) 'e' ((:) 'q' ([])))))) (Cons (Pair GHC.Base.False (Inl (TyVar
    ((:) 'A' ([]))))) (Cons (Pair GHC.Base.False (Inl (TyVar ((:) 'x'
    ([]))))) (Cons (Pair GHC.Base.False (Inl (TyVar ((:) 'A' ([]))))) (Cons
    (Pair GHC.Base.False (Inl (TyVar ((:) 'y' ([]))))) Nil)))))) (TMu None
    (TVar0 ((:) 'H' ([]))) (Some (TyLamK (Named ((:) 'A' ((:) '1' ([]))))
    (Some KdStar) (TyLam (Named ((:) 'y' ((:) '1' ([])))) (Some (TyVar ((:)
    'A' ((:) '1' ([]))))) (TyLam Anon (Some (TyApp (TyVar ((:) 'J' ((:) 'M'
    ((:) 'e' ((:) 'q' ([])))))) (Cons (Pair GHC.Base.False (Inl (TyVar ((:)
    'A' ([]))))) (Cons (Pair GHC.Base.False (Inl (TyVar ((:) 'x' ([])))))
    (Cons (Pair GHC.Base.False (Inl (TyVar ((:) 'A' ((:) '1' ([])))))) (Cons
    (Pair GHC.Base.False (Inl (TyVar ((:) 'y' ((:) '1' ([])))))) Nil))))))
    (TyApp (TyVar ((:) 'P' ([]))) (Cons (Pair GHC.Base.False (Inl (TyVar ((:)
    'y' ([]))))) Nil)))))) (Cons (Pair (TVar0 ((:) 'J' ((:) 'M' ((:) 'e' ((:)
    'q' ((:) '_' ((:) 'r' ((:) 'e' ((:) 'f' ((:) 'l' ([]))))))))))) (TLetTm
    (Named ((:) 'H' ([]))) GHC.Base.False (TyEq (TVar0 ((:) 'y' ([]))) (TVar0
    ((:) 'x' ([])))) (TMu None (TVar0 ((:) 'H' ([]))) None (Cons (Pair (TVar0
    ((:) 'J' ((:) 'M' ((:) 'e' ((:) 'q' ((:) '_' ((:) 'r' ((:) 'e' ((:) 'f'
    ((:) 'l' ([]))))))))))) TBeta) Nil)) (TRho (TVar0 ((:) 'H' ([]))) (TVar0
    ((:) 'p' ([])))))) Nil))))))))

merge :: (List GHC.Base.Int) -> (List GHC.Base.Int) -> List GHC.Base.Int
merge l1 l2 =
  let {
   merge_aux l3 =
     case l1 of {
      Nil -> l3;
      Cons a1 l1' ->
       case l3 of {
        Nil -> l1;
        Cons a2 l2' ->
         case let {
               leb x y =
                 (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                   (\_ -> GHC.Base.True)
                   (\x' ->
                   (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
                     (\_ -> GHC.Base.False)
                     (\y' -> leb x' y')
                     y)
                   x}
              in leb a1 a2 of {
          GHC.Base.True -> Cons a1 (merge l1' l3);
          GHC.Base.False -> Cons a2 (merge_aux l2')}}}}
  in merge_aux l2

merge_list_to_stack :: (List (Option (List GHC.Base.Int))) -> (List
                       GHC.Base.Int) -> List (Option (List GHC.Base.Int))
merge_list_to_stack stack l =
  case stack of {
   Nil -> Cons (Some l) Nil;
   Cons y stack' ->
    case y of {
     Some l' -> Cons None (merge_list_to_stack stack' (merge l' l));
     None -> Cons (Some l) stack'}}

merge_stack :: (List (Option (List GHC.Base.Int))) -> List GHC.Base.Int
merge_stack stack =
  case stack of {
   Nil -> Nil;
   Cons y stack' ->
    case y of {
     Some l -> merge l (merge_stack stack');
     None -> merge_stack stack'}}

iter_merge :: (List (Option (List GHC.Base.Int))) -> (List GHC.Base.Int) ->
              List GHC.Base.Int
iter_merge stack l =
  case l of {
   Nil -> merge_stack stack;
   Cons a l' -> iter_merge (merge_list_to_stack stack (Cons a Nil)) l'}

sort :: (List GHC.Base.Int) -> List GHC.Base.Int
sort =
  iter_merge Nil

flatten_stack :: (List (Option (List GHC.Base.Int))) -> List GHC.Base.Int
flatten_stack stack =
  case stack of {
   Nil -> Nil;
   Cons o stack' ->
    case o of {
     Some l -> app l (flatten_stack stack');
     None -> flatten_stack stack'}}

inj1M :: (Monad a3) -> a3 -> a3
inj1M h m =
  fmap (functor_Monad h) (\x -> Inl x) m

inj2M :: (Monad a3) -> a3 -> a3
inj2M h m =
  fmap (functor_Monad h) (\x -> Inr x) m

type Ctx = List Var0

string_RelDec :: RelDec Prelude.String
string_RelDec =
  (Prelude.==)

string_of_list_ascii :: (List Prelude.Char) -> Prelude.String
string_of_list_ascii s =
  case s of {
   Nil -> ([]);
   Cons ch s0 -> (:) ch (string_of_list_ascii s0)}

list_ascii_of_string :: Prelude.String -> List Prelude.Char
list_ascii_of_string s =
  case s of {
   ([]) -> Nil;
   (:) ch s0 -> Cons ch (list_ascii_of_string s0)}

revStr :: Prelude.String -> Prelude.String
revStr s =
  string_of_list_ascii (rev0 (list_ascii_of_string s))

type A_rargs = Alist Var0 Prelude.String

type A_rargspos = Alist Var0 GHC.Base.Int

type A_nrargs = Alist Var0 (List (Prod Var0 (Sum Kind Typ)))

type A_motives = Alist Var0 Typ

type A_reorg = Alist Var0 (List GHC.Base.Int)

type Rec_env =
  Prod (Prod (Prod (Prod A_rargs A_rargspos) A_nrargs) A_motives) A_reorg

type Params_env = Alist Var0 GHC.Base.Int

fresh_renv :: Rec_env
fresh_renv =
  Pair (Pair (Pair (Pair Nil Nil) Nil) Nil) Nil

type M a =
  StateT Params_env
  (ReaderT (Prod (Prod Global_env Ctx) Rec_env)
  (EitherT Prelude.String (Ident0 Any) Any) Any) a

run_m :: Params_env -> (Prod (Prod Global_env Ctx) Rec_env) -> (M a1) -> Sum
         Prelude.String (Prod a1 Params_env)
run_m params env ev =
  unIdent (unEitherT (runReaderT (runStateT (unsafeCoerce ev) params) env))

getName :: Name0 -> Var0
getName n =
  case n of {
   Anon -> (:) '_' ([]);
   Named c -> c}

list_m :: (Monad a2) -> (List a2) -> a2
list_m h l =
  case l of {
   Nil -> ret h Nil;
   Cons x xs ->
    bind h x (\x' -> bind h (list_m h xs) (\xs' -> ret h (Cons x' xs')))}

option_m :: (Monad (M Any)) -> (MonadExc Prelude.String (M Any)) -> (Option
            a1) -> Prelude.String -> M a1
option_m monad_m either_m x s =
  case x of {
   Some y -> ret (unsafeCoerce monad_m) y;
   None -> raise (unsafeCoerce either_m) s}

kername_to_qualid :: Prelude.String -> Prelude.String
kername_to_qualid s =
  case index 0 ((:) '.' ([])) (revStr s) of {
   Some n -> let {s_len = length0 s} in substring (sub s_len n) s_len s;
   None -> s}

isKind :: Term -> GHC.Base.Bool
isKind t =
  case t of {
   TSort _ -> GHC.Base.True;
   TProd _ _ t2 -> isKind t2;
   _ -> GHC.Base.False}

lookup_constant :: Ident -> Global_env -> Option Constant_body
lookup_constant id0 decls =
  case decls of {
   Nil -> None;
   Cons g tl ->
    case g of {
     ConstantDecl kn d ->
      case (Prelude.==) kn id0 of {
       GHC.Base.True -> Some d;
       GHC.Base.False -> lookup_constant id0 tl};
     InductiveDecl _ _ -> lookup_constant id0 tl}}

isType :: (Monad (M Any)) -> (MonadReader
          (Prod (Prod Global_env Ctx) Rec_env) (M Any)) -> (MonadExc
          Prelude.String (M Any)) -> Term -> M GHC.Base.Bool
isType monad_m reader_m either_m t =
  bind (unsafeCoerce monad_m) (ask (unsafeCoerce reader_m)) (\x ->
    case x of {
     Pair y _ ->
      case y of {
       Pair genv _ ->
        case t of {
         TProd _ t1 t2 ->
          bind (unsafeCoerce monad_m) (isType monad_m reader_m either_m t1)
            (\b1 ->
            bind (unsafeCoerce monad_m) (isType monad_m reader_m either_m t2)
              (\b2 -> ret (unsafeCoerce monad_m) (andb b1 b2)));
         TApp t0 _ -> isType monad_m reader_m either_m t0;
         TConst kern _ ->
          bind (unsafeCoerce monad_m)
            (option_m monad_m either_m
              (unsafeCoerce lookup_constant kern genv) ((:) 'C' ((:) 'o' ((:)
              'u' ((:) 'l' ((:) 'd' ((:) 'n' ((:) '\'' ((:) 't' ((:) ' ' ((:)
              'f' ((:) 'i' ((:) 'n' ((:) 'd' ((:) ' ' ((:) 'c' ((:) 'd' ((:)
              'e' ((:) 'c' ((:) 'l' ((:) ' ' ((:) 'b' ((:) 'o' ((:) 'd' ((:)
              'y' ([])))))))))))))))))))))))))) (\cdecl ->
            let {cdecl_ty = cst_type cdecl} in
            ret (unsafeCoerce monad_m) (isKind cdecl_ty));
         TInd _ _ -> ret (unsafeCoerce monad_m) GHC.Base.True;
         _ -> ret (unsafeCoerce monad_m) GHC.Base.False}}})

decl_exists :: Ident -> Global_env -> GHC.Base.Bool
decl_exists id0 decls =
  case decls of {
   Nil -> GHC.Base.False;
   Cons g tl ->
    case g of {
     ConstantDecl kn _ ->
      orb ((Prelude.==) (kername_to_qualid kn) id0) (decl_exists id0 tl);
     InductiveDecl kn d ->
      case (Prelude.==) (kername_to_qualid kn) id0 of {
       GHC.Base.True -> GHC.Base.True;
       GHC.Base.False ->
        let {
         exists_constr = let {
                          exists_constr l =
                            case l of {
                             Nil -> GHC.Base.False;
                             Cons p0 tl0 ->
                              case p0 of {
                               Pair p1 _ ->
                                case p1 of {
                                 Pair c _ ->
                                  orb ((Prelude.==) c id0)
                                    (exists_constr tl0)}}}}
                         in exists_constr}
        in
        let {bdy = ind_bodies d} in
        case hd_error bdy of {
         Some b -> orb (exists_constr (ind_ctors b)) (decl_exists id0 tl);
         None -> decl_exists id0 tl}}}}

bound_var :: Ident -> Ctx -> GHC.Base.Bool
bound_var x _UU0393_ =
  case _UU0393_ of {
   Nil -> GHC.Base.False;
   Cons x' xs -> orb ((Prelude.==) x x') (bound_var x xs)}

fresh :: (Monad (M Any)) -> (MonadReader (Prod (Prod Global_env Ctx) Rec_env)
         (M Any)) -> Ident -> M Ident
fresh monad_m reader_m x =
  bind (unsafeCoerce monad_m) (ask (unsafeCoerce reader_m)) (\x0 ->
    case x0 of {
     Pair y _ ->
      case y of {
       Pair genv _UU0393_ ->
        case orb (bound_var x _UU0393_) (decl_exists x genv) of {
         GHC.Base.True ->
          ret (unsafeCoerce monad_m) (append x ((:) '\'' ([])));
         GHC.Base.False -> ret (unsafeCoerce monad_m) x}}})

localDenote :: (Monad (M Any)) -> (MonadReader
               (Prod (Prod Global_env Ctx) Rec_env) (M Any)) -> Name -> (M
               a1) -> M (Prod a1 Name0)
localDenote monad_m reader_m x r =
  case x of {
   NAnon ->
    bind (unsafeCoerce monad_m)
      (local (unsafeCoerce reader_m) (\pat ->
        case pat of {
         Pair y renv ->
          case y of {
           Pair genv _UU0393_ -> Pair (Pair genv (Cons ((:) '_' ([]))
            _UU0393_)) renv}}) (unsafeCoerce r)) (\r' ->
      ret (unsafeCoerce monad_m) (Pair r' Anon));
   NNamed n ->
    bind (unsafeCoerce monad_m) (unsafeCoerce fresh monad_m reader_m n)
      (\x' ->
      bind (unsafeCoerce monad_m)
        (local (unsafeCoerce reader_m) (\pat ->
          case pat of {
           Pair y renv ->
            case y of {
             Pair genv _UU0393_ -> Pair (Pair genv (Cons x' _UU0393_)) renv}})
          (unsafeCoerce r)) (\r' ->
        ret (unsafeCoerce monad_m) (Pair r' (Named x'))))}

take_args' :: (Monad (M Any)) -> (MonadReader
              (Prod (Prod Global_env Ctx) Rec_env) (M Any)) -> (MonadExc
              Prelude.String (M Any)) -> (List (Sum Typ Term0)) ->
              GHC.Base.Int -> Term -> M (List (Sum Typ Term0))
take_args' monad_m reader_m either_m acc n t =
  (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
    (\_ -> ret (unsafeCoerce monad_m) acc)
    (\n' ->
    case t of {
     TLambda x ty t' ->
      bind (unsafeCoerce monad_m)
        (unsafeCoerce fresh monad_m reader_m (get_ident x)) (\x' ->
        bind (unsafeCoerce monad_m)
          (unsafeCoerce isType monad_m reader_m either_m ty) (\b ->
          case b of {
           GHC.Base.True ->
            take_args' monad_m reader_m either_m (Cons (Inl (TyVar x')) acc)
              n' t';
           GHC.Base.False ->
            take_args' monad_m reader_m either_m (Cons (Inr (TVar0 x')) acc)
              n' t'}));
     _ -> ret (unsafeCoerce monad_m) acc})
    n

type Ctor_typ = Prod (Prod Ident Term) GHC.Base.Int

take_args :: (Monad (M Any)) -> (MonadReader
             (Prod (Prod Global_env Ctx) Rec_env) (M Any)) -> (MonadExc
             Prelude.String (M Any)) -> (Prod GHC.Base.Int Term) -> M
             (List (Sum Typ Term0))
take_args monad_m reader_m either_m brch =
  case brch of {
   Pair nargs t ->
    bind (unsafeCoerce monad_m)
      (take_args' monad_m reader_m either_m Nil nargs t) (\args ->
      ret (unsafeCoerce monad_m) (rev0 args))}

get_ctors :: (Monad (M Any)) -> (MonadReader
             (Prod (Prod Global_env Ctx) Rec_env) (M Any)) -> (MonadExc
             Prelude.String (M Any)) -> Inductive -> M (List Ctor_typ)
get_ctors monad_m reader_m either_m ind =
  bind (unsafeCoerce monad_m) (ask (unsafeCoerce reader_m)) (\x ->
    case x of {
     Pair y _ ->
      case y of {
       Pair genv _ ->
        let {minds = inductive_mind ind} in
        bind (unsafeCoerce monad_m)
          (option_m monad_m either_m
            (unsafeCoerce lookup_mind_decl minds genv) ((:) 'D' ((:) 'e' ((:)
            'c' ((:) 'l' ((:) 'a' ((:) 'r' ((:) 'a' ((:) 't' ((:) 'i' ((:)
            'o' ((:) 'n' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:)
            'f' ((:) 'o' ((:) 'u' ((:) 'n' ((:) 'd'
            ([]))))))))))))))))))))))) (\m_decl ->
          let {bodies = ind_bodies m_decl} in
          bind (unsafeCoerce monad_m)
            (option_m monad_m either_m (hd_error (unsafeCoerce bodies)) ((:)
              'C' ((:) 'o' ((:) 'u' ((:) 'l' ((:) 'd' ((:) ' ' ((:) 'n' ((:)
              'o' ((:) 't' ((:) ' ' ((:) 'f' ((:) 'i' ((:) 'n' ((:) 'd' ((:)
              ' ' ((:) 'd' ((:) 'e' ((:) 'c' ((:) 'l' ((:) 'a' ((:) 'r' ((:)
              'a' ((:) 't' ((:) 'i' ((:) 'o' ((:) 'n' ((:) ' ' ((:) 'b' ((:)
              'o' ((:) 'd' ((:) 'y' ([])))))))))))))))))))))))))))))))))
            (\body -> ret (unsafeCoerce monad_m) (ind_ctors body)))}})

build_tApp :: (Prod Ctor_typ (List (Sum Typ Term0))) -> Term0
build_tApp nts =
  case nts of {
   Pair ctor ts ->
    case ctor of {
     Pair p0 _ ->
      case p0 of {
       Pair n _ -> TApp0 (TVar0 n) (map (\t -> Pair GHC.Base.False t) ts)}}}

removeLambdas :: GHC.Base.Int -> Term0 -> Term0
removeLambdas n t =
  (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
    (\_ -> t)
    (\n' ->
    case t of {
     TLam _ _ _ t' -> removeLambdas n' t';
     TLamK _ _ t' -> removeLambdas n' t';
     _ -> t})
    n

showList' :: (List Prelude.String) -> Prelude.String
showList' ls =
  case ls of {
   Nil -> ([]);
   Cons x xs -> append x (append ((:) ',' ((:) ' ' ([]))) (showList' xs))}

showList :: (List Prelude.String) -> Prelude.String
showList ls =
  append ((:) '[' ((:) ' ' ([]))) (append (showList' ls) ((:) ']' ([])))

defaultTy :: Typ
defaultTy =
  TyVar ((:) 'x' ((:) 'x' ([])))

is_delta :: Term -> GHC.Base.Bool
is_delta t =
  case t of {
   TLetIn _ t' kty _ ->
    case kty of {
     TInd s _ ->
      case (Prelude.==) ((:) 'C' ((:) 'o' ((:) 'q' ((:) '.' ((:) 'I' ((:) 'n'
             ((:) 'i' ((:) 't' ((:) '.' ((:) 'L' ((:) 'o' ((:) 'g' ((:) 'i'
             ((:) 'c' ((:) '.' ((:) 'F' ((:) 'a' ((:) 'l' ((:) 's' ((:) 'e'
             ([]))))))))))))))))))))) (inductive_mind s) of {
       GHC.Base.True ->
        case t' of {
         TApp f _ ->
          case f of {
           TConst s' _ ->
            (Prelude.==) ((:) 'C' ((:) 'o' ((:) 'q' ((:) '.' ((:) 'I' ((:)
              'n' ((:) 'i' ((:) 't' ((:) '.' ((:) 'L' ((:) 'o' ((:) 'g' ((:)
              'i' ((:) 'c' ((:) '.' ((:) 'e' ((:) 'q' ((:) '_' ((:) 'i' ((:)
              'n' ((:) 'd' ([])))))))))))))))))))))) s';
           _ -> GHC.Base.True};
         _ -> GHC.Base.True};
       GHC.Base.False -> GHC.Base.False};
     _ -> GHC.Base.False};
   _ -> GHC.Base.False}

get_rfunc_name :: Term0 -> A_rargs -> Option Var0
get_rfunc_name t rarg0 =
  case t of {
   TVar0 x -> alist_find string_RelDec x rarg0;
   _ -> None}

get_motive :: (Option Ident) -> A_motives -> Typ -> Typ
get_motive x mfty default0 =
  case x of {
   Some x' ->
    case alist_find string_RelDec x' mfty of {
     Some mot -> mot;
     None -> default0};
   None -> default0}

eraseNones :: (List (Option a1)) -> List a1
eraseNones ls =
  case ls of {
   Nil -> Nil;
   Cons o l ->
    case o of {
     Some x -> Cons x (eraseNones l);
     None -> eraseNones l}}

delete_nth :: (List a1) -> GHC.Base.Int -> List a1
delete_nth l n =
  case l of {
   Nil -> Nil;
   Cons x xs ->
    (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
      (\_ -> xs)
      (\n' -> Cons x (delete_nth xs n'))
      n}

nth_many :: (List a1) -> (List GHC.Base.Int) -> List a1
nth_many l r =
  eraseNones (map (nth_error l) r)

delete_many :: (List a1) -> (List GHC.Base.Int) -> List a1
delete_many l dels =
  fold_right (\a l' -> delete_nth l' a) l dels

tag_last :: (List a1) -> List (Prod GHC.Base.Bool a1)
tag_last l =
  case l of {
   Nil -> Nil;
   Cons a1 l0 ->
    case l0 of {
     Nil -> Cons (Pair GHC.Base.False a1) Nil;
     Cons _ _ -> Cons (Pair GHC.Base.True a1) (tag_last l0)}}

reorg_app_args :: (Monad (M Any)) -> (MonadReader
                  (Prod (Prod Global_env Ctx) Rec_env) (M Any)) -> Term0 ->
                  (List a1) -> M (List (Prod GHC.Base.Bool a1))
reorg_app_args monad_m reader_m t l =
  let {tag = map (\x -> Pair GHC.Base.False x)} in
  case t of {
   TVar0 x ->
    bind (unsafeCoerce monad_m) (ask (unsafeCoerce reader_m)) (\x0 ->
      case x0 of {
       Pair _ renv ->
        case renv of {
         Pair _ reorg ->
          case alist_find string_RelDec x reorg of {
           Some re ->
            let {items = tag_last (nth_many l re)} in
            let {sorted_re = sort re} in
            let {tail = delete_many l sorted_re} in
            ret (unsafeCoerce monad_m) (app items (tag tail));
           None -> ret (unsafeCoerce monad_m) (tag l)}}});
   _ -> ret (unsafeCoerce monad_m) (tag l)}

tyAppVars' :: (List (Sum Typ Term0)) -> List (Option Var0)
tyAppVars' ts =
  let {
   peel = \t ->
    case t of {
     Inl y -> case y of {
               TyVar x -> Some x;
               _ -> None};
     Inr y -> case y of {
               TVar0 x -> Some x;
               _ -> None}}}
  in
  case ts of {
   Nil -> Nil;
   Cons t ts0 -> Cons (peel t) (tyAppVars' ts0)}

tyAppVars :: (List (Sum Typ Term0)) -> List Var0
tyAppVars x =
  eraseNones (tyAppVars' x)

app_inl :: (a1 -> a3) -> (Sum a1 a2) -> Option a3
app_inl f x =
  case x of {
   Inl a -> Some (f a);
   Inr _ -> None}

map_inl :: (a1 -> a4) -> (List (Prod a3 (Sum a1 a2))) -> List a4
map_inl f l =
  eraseNones (map (\pat -> case pat of {
                            Pair _ ab -> app_inl f ab}) l)

map_pair :: (a1 -> a2) -> (Prod a1 a1) -> Prod a2 a2
map_pair f pat =
  case pat of {
   Pair a1 a2 -> Pair (f a1) (f a2)}

delparamsTy :: Params_env -> Typ -> Typ
delparamsTy penv ty =
  let {dparTy = delparamsTy penv} in
  let {dparT = delparamsT penv} in
  let {dparK = delparamsK penv} in
  let {
   c = \bkt ->
    case bkt of {
     Pair b kt ->
      case kt of {
       Inl ty0 -> Pair b (Inl (dparTy ty0));
       Inr t -> Pair b (Inr (dparT t))}}}
  in
  case ty of {
   TyVar _ -> ty;
   TyAll x k b -> TyAll x (dparK k) (dparTy b);
   TyPi x ty' b -> TyPi x (dparTy ty') (dparTy b);
   TyApp t' apps ->
    case t' of {
     TyVar x ->
      case alist_find string_RelDec x penv of {
       Some n -> TyApp (TyVar x) (skipn n apps);
       None -> TyApp (TyVar x) (map c apps)};
     _ -> TyApp t' (map c apps)};
   TyLam x ty' b ->
    let {ty'' = case ty' of {
                 Some u -> Some (dparTy u);
                 None -> None}} in
    TyLam x ty'' (dparTy b);
   TyLamK x k b ->
    let {k' = case k of {
               Some u -> Some (dparK u);
               None -> None}} in
    TyLamK x k' (dparTy b);
   TyAllT x ty0 b -> TyAllT x (dparTy ty0) (dparTy b);
   TyIntersec x ty' b -> TyIntersec x (dparTy ty') (dparTy b);
   TyEq t1 _ -> TyEq (delparamsT penv t1) (delparamsT penv t1)}

delparamsK :: Params_env -> Kind -> Kind
delparamsK penv k =
  case k of {
   KdStar -> KdStar;
   KdAll x kty k' ->
    let {
     kty' = case kty of {
             Inl ki -> Inl ki;
             Inr ty -> Inr (delparamsTy penv ty)}}
    in
    KdAll x kty' (delparamsK penv k')}

delparamsT :: Params_env -> Term0 -> Term0
delparamsT penv t =
  let {dparTy = delparamsTy penv} in
  let {dparT = delparamsT penv} in
  let {dparK = delparamsK penv} in
  let {
   c = \bkt ->
    case bkt of {
     Pair b kt ->
      case kt of {
       Inl ty -> Pair b (Inl (dparTy ty));
       Inr t0 -> Pair b (Inr (dparT t0))}}}
  in
  case t of {
   TVar0 _ -> t;
   TLam x er ty b ->
    let {ty'' = case ty of {
                 Some u -> Some (dparTy u);
                 None -> None}} in
    TLam x er ty'' (dparT b);
   TLamK x k b ->
    let {k' = case k of {
               Some u -> Some (dparK u);
               None -> None}} in
    TLamK x k' (dparT b);
   TApp0 t0 apps -> TApp0 (dparT t0) (map c apps);
   TLetTm x er ty t' b -> TLetTm x er (dparTy ty) (dparT t') (dparT b);
   TLetTy x k ty b -> TLetTy x k (dparTy ty) (dparT b);
   TMu x t' mot bs -> TMu x (dparT t') (option_map dparTy mot)
    (map (map_pair dparT) bs);
   TDelta b -> TDelta (dparT b);
   TRho t1 t2 -> TRho (dparT t1) (dparT t2);
   TBeta -> TBeta}

get_depsTy :: Typ -> List Var0
get_depsTy ty =
  case ty of {
   TyVar x -> Cons x Nil;
   TyAll _ _ t' -> get_depsTy t';
   TyPi _ t1 t2 -> app (get_depsTy t1) (get_depsTy t2);
   TyApp t' apps ->
    app (get_depsTy t')
      (app (concat (map_inl get_depsTy apps)) (tyAppVars (map snd apps)));
   TyLam _ t1 t2 ->
    app (get_depsTy t2) (case t1 of {
                          Some u -> get_depsTy u;
                          None -> Nil});
   TyLamK _ _ t' -> get_depsTy t';
   TyAllT _ _ t' -> get_depsTy t';
   TyIntersec _ t1 t2 -> app (get_depsTy t1) (get_depsTy t2);
   TyEq _ _ -> Nil}

get_deps :: Params_env -> (Sum Kind Typ) -> List Var0
get_deps penv kty =
  case kty of {
   Inl _ -> Nil;
   Inr ty -> get_depsTy (delparamsTy penv ty)}

type Mot_env = Alist Var0 (Sum Kind Typ)

build_env' :: Typ -> Mot_env -> Mot_env
build_env' ty acc =
  case ty of {
   TyAll n k b ->
    build_env' b (alist_add string_RelDec (getName n) (Inl k) acc);
   TyPi n ty0 b ->
    build_env' b (alist_add string_RelDec (getName n) (Inr ty0) acc);
   _ -> acc}

get_body :: Typ -> Typ
get_body t =
  case t of {
   TyAll _ _ b -> get_body b;
   TyPi _ _ b -> get_body b;
   _ -> t}

build_env :: Typ -> List (Prod Var0 (Sum Kind Typ))
build_env t =
  rev0 (build_env' t Nil)

insert_pi_body :: Typ -> Var0 -> (Sum Kind Typ) -> Typ
insert_pi_body t x kty =
  case t of {
   TyLam x' ty' b -> TyLam x' ty' (insert_pi_body b x kty);
   _ ->
    case kty of {
     Inl k -> TyAll (Named x) k t;
     Inr ty -> TyPi (Named x) ty t}}

insert_lam_body :: Typ -> Var0 -> (Sum Kind Typ) -> Typ
insert_lam_body t x kty =
  case kty of {
   Inl k -> TyLamK (Named x) (Some k) t;
   Inr ty -> TyLam (Named x) (Some ty) t}

unfold_env :: Typ -> Mot_env -> Typ
unfold_env t env =
  fold_right (\pat t' -> case pat of {
                          Pair x ty -> insert_pi_body t' x ty}) t env

alist_remove_many :: (List Var0) -> Mot_env -> Alist Var0 (Sum Kind Typ)
alist_remove_many l env =
  fold_right (\x env' -> alist_remove string_RelDec x env') env l

alist_find_many :: (List Var0) -> Mot_env -> List (Option (Sum Kind Typ))
alist_find_many l env =
  case l of {
   Nil -> Nil;
   Cons x xs -> Cons (alist_find string_RelDec x env)
    (alist_find_many xs env)}

combine_maybe :: (List a1) -> (List (Option a2)) -> List (Prod a1 a2)
combine_maybe xs ys =
  case xs of {
   Nil -> Nil;
   Cons x xs0 ->
    case ys of {
     Nil -> Nil;
     Cons o ys0 ->
      case o of {
       Some y -> Cons (Pair x y) (combine_maybe xs0 ys0);
       None -> combine_maybe xs0 ys0}}}

build_lam :: Typ -> Mot_env -> Typ
build_lam t env =
  fold_right (\pat t' -> case pat of {
                          Pair x ty -> insert_lam_body t' x ty}) t env

alist_pos' :: (RelDec a1) -> GHC.Base.Int -> (Alist a1 a2) -> a1 -> Option
              GHC.Base.Int
alist_pos' h acc m k =
  case m of {
   Nil -> None;
   Cons p0 ms ->
    case p0 of {
     Pair k' _ ->
      case rel_dec h k k' of {
       GHC.Base.True -> Some acc;
       GHC.Base.False -> alist_pos' h ((\ x -> x Prelude.+ 1) acc) ms k}}}

alist_pos :: (RelDec a1) -> (Alist a1 a2) -> a1 -> Option GHC.Base.Int
alist_pos rD_K =
  alist_pos' rD_K 0

pull_deps_func :: (Monad (M Any)) -> (MonadReader
                  (Prod (Prod Global_env Ctx) Rec_env) (M Any)) ->
                  (MonadState Params_env (M Any)) -> (MonadExc Prelude.String
                  (M Any)) -> (SigT Typ
                  (SigT (List Var0)
                  (SigT (List (Prod Var0 (Sum Kind Typ))) Params_env))) ->
                  Prod Typ (Alist Var0 (Sum Kind Typ))
pull_deps_func monad_m reader_m state_m either_m x =
  let {t = projT1 x} in
  let {deps = projT1 (projT2 x)} in
  let {fvars = projT1 (projT2 (projT2 x))} in
  let {penv = projT2 (projT2 (projT2 x))} in
  let {
   pull_deps0 = \t0 deps0 fvars0 penv0 ->
    let {y = ExistT t0 (ExistT deps0 (ExistT fvars0 penv0))} in
    pull_deps_func monad_m reader_m state_m either_m (proj1_sig y)}
  in
  let {fvars' = alist_remove_many deps fvars} in
  let {deps_ty = alist_find_many deps fvars} in
  let {ts = combine_maybe deps deps_ty} in
  let {t' = build_lam t ts} in
  let {tys = map snd ts} in
  let {deps' = concat (map (get_deps penv) tys)} in
  case eq_nat (length deps') 0 of {
   GHC.Base.True -> Pair t' fvars';
   GHC.Base.False -> pull_deps0 t' deps' fvars' penv}

pull_deps :: (Monad (M Any)) -> (MonadReader
             (Prod (Prod Global_env Ctx) Rec_env) (M Any)) -> (MonadState
             Params_env (M Any)) -> (MonadExc Prelude.String (M Any)) -> Typ
             -> (List Var0) -> (List (Prod Var0 (Sum Kind Typ))) ->
             Params_env -> Prod Typ (Alist Var0 (Sum Kind Typ))
pull_deps monad_m reader_m state_m either_m t deps fvars penv =
  pull_deps_func monad_m reader_m state_m either_m (ExistT t (ExistT deps
    (ExistT fvars penv)))

get_lambodies :: Typ -> List Var0
get_lambodies t =
  case t of {
   TyLam x _ b -> Cons (getName x) (get_lambodies b);
   TyLamK x _ b -> Cons (getName x) (get_lambodies b);
   _ -> Nil}

denoteMotive :: (Monad (M Any)) -> (MonadReader
                (Prod (Prod Global_env Ctx) Rec_env) (M Any)) -> (MonadState
                Params_env (M Any)) -> (MonadExc Prelude.String (M Any)) ->
                Typ -> GHC.Base.Int -> Prelude.String -> M Rec_env
denoteMotive monad_m reader_m state_m either_m mot rargpos fname =
  let {body = get_body mot} in
  let {fvars = build_env mot} in
  bind (unsafeCoerce monad_m) (get (unsafeCoerce state_m)) (\penv ->
    bind (unsafeCoerce monad_m)
      (option_m monad_m either_m (nth_error (unsafeCoerce fvars) rargpos)
        (append ((:) 'e' ((:) 'r' ((:) 'r' ((:) 'o' ((:) 'r' ((:) ' ' ((:)
          'f' ((:) 'e' ((:) 't' ((:) 'c' ((:) 'h' ((:) 'i' ((:) 'n' ((:) 'g'
          ((:) ' ' ((:) 'r' ((:) 'e' ((:) 'c' ((:) 'u' ((:) 'r' ((:) 's' ((:)
          'i' ((:) 'v' ((:) 'e' ((:) ' ' ((:) 'a' ((:) 'r' ((:) 'g' ((:) 'u'
          ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:) ' ' ((:) 'n' ((:) 'a' ((:)
          'm' ((:) 'e' ((:) ' ' ((:) 'f' ((:) 'o' ((:) 'r' ((:) ' ' ((:) 'm'
          ((:) 'o' ((:) 't' ((:) 'i' ((:) 'v' ((:) 'e' ((:) ' ' ((:) 'i' ((:)
          'n' ((:) ' '
          ([]))))))))))))))))))))))))))))))))))))))))))))))))))))))
          (showList (map fst fvars)))) (\x ->
      case x of {
       Pair rarg0 rarg_ty ->
        let {nargs = alist_remove string_RelDec rarg0 fvars} in
        let {deps = get_deps penv rarg_ty} in
        let {t' = insert_lam_body body rarg0 rarg_ty} in
        case pull_deps monad_m reader_m state_m either_m t' deps nargs penv of {
         Pair t'' nargs' ->
          let {boundvars = get_lambodies t''} in
          let {reorgs = map (alist_pos string_RelDec fvars) boundvars} in
          let {mot' = unfold_env t'' nargs'} in
          bind (unsafeCoerce monad_m) (ask (unsafeCoerce reader_m)) (\x0 ->
            case x0 of {
             Pair _ y0 ->
              case y0 of {
               Pair y reorg ->
                case y of {
                 Pair y1 amots ->
                  case y1 of {
                   Pair y2 anargs ->
                    case y2 of {
                     Pair arargs arpos ->
                      let {
                       renv' = Pair (Pair (Pair (Pair
                        (alist_add string_RelDec rarg0 fname arargs)
                        (alist_add string_RelDec fname rargpos arpos))
                        (alist_add string_RelDec fname nargs' anargs))
                        (alist_add string_RelDec fname mot' amots))
                        (alist_add string_RelDec fname (eraseNones reorgs)
                          reorg)}
                      in
                      ret (unsafeCoerce monad_m) renv'}}}}})}}))

flattenTApp :: Term0 -> Term0
flattenTApp t =
  case t of {
   TApp0 t' l -> case l of {
                  Nil -> t';
                  Cons _ _ -> t};
   _ -> t}

get_nrargs :: (Option Var0) -> A_nrargs -> List (Prod Var0 (Sum Kind Typ))
get_nrargs fname nrargs =
  case fname of {
   Some x ->
    case alist_find string_RelDec x nrargs of {
     Some l -> l;
     None -> Nil};
   None -> Nil}

bind_nrargs :: (List (Prod Var0 (Sum Kind Typ))) -> Term0 -> Term0
bind_nrargs nrargs tail =
  let {fresh0 = \x -> append x ((:) '\'' ([]))} in
  case nrargs of {
   Nil -> tail;
   Cons p0 ts ->
    case p0 of {
     Pair x s ->
      case s of {
       Inl _ -> TLamK (Named (fresh0 x)) None (bind_nrargs ts tail);
       Inr _ -> TLam (Named ((:) '_' ([]))) GHC.Base.False None
        (bind_nrargs ts tail)}}}

denoteKind :: (Monad (M Any)) -> (MonadReader
              (Prod (Prod Global_env Ctx) Rec_env) (M Any)) -> (MonadState
              Params_env (M Any)) -> (MonadExc Prelude.String (M Any)) ->
              Term -> M Kind
denoteKind monad_m reader_m state_m either_m =
  let {
   denoteKind0 t =
     case t of {
      TSort _ -> ret (unsafeCoerce monad_m) KdStar;
      TProd x t1 t2 ->
       bind (unsafeCoerce monad_m)
         (case isKind t1 of {
           GHC.Base.True ->
            fmap (functor_Monad (unsafeCoerce monad_m)) (\x0 -> Inl x0)
              (denoteKind0 t1);
           GHC.Base.False ->
            fmap (functor_Monad (unsafeCoerce monad_m)) (\x0 -> Inr x0)
              (denoteType0 t1)}) (\k1 ->
         bind (unsafeCoerce monad_m)
           (unsafeCoerce localDenote monad_m reader_m x (denoteKind0 t2))
           (\x0 ->
           case x0 of {
            Pair k2 x' -> ret (unsafeCoerce monad_m) (KdAll x' k1 k2)}));
      _ ->
       raise (unsafeCoerce either_m) ((:) 'I' ((:) 'l' ((:) 'l' ((:) '-' ((:)
         'f' ((:) 'o' ((:) 'r' ((:) 'm' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'k'
         ((:) 'i' ((:) 'n' ((:) 'd' ([]))))))))))))))))};
   denoteType0 t =
     case t of {
      TRel n ->
       bind (unsafeCoerce monad_m) (ask (unsafeCoerce reader_m)) (\x ->
         case x of {
          Pair y _ ->
           case y of {
            Pair _ _UU0393_ ->
             bind (unsafeCoerce monad_m)
               (option_m monad_m either_m
                 (nth_error (unsafeCoerce _UU0393_) n)
                 (append ((:) 't' ((:) 'y' ((:) ' ' ((:) 't' ((:) 'R' ((:)
                   'e' ((:) 'l' ((:) ' ' ([])))))))))
                   (append (string_of_nat n)
                     (append ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' '
                       ((:) 'i' ((:) 'n' ((:) ' ' ((:) 'e' ((:) 'n' ((:) 'v'
                       ((:) 'i' ((:) 'r' ((:) 'o' ((:) 'n' ((:) 'm' ((:) 'e'
                       ((:) 'n' ((:) 't' ((:) ' ' ([])))))))))))))))))))))
                       (showList _UU0393_))))) (\v ->
               ret (unsafeCoerce monad_m) (TyVar v))}});
      TVar _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:)
         ' ' ((:) 't' ((:) 'V' ((:) 'a' ((:) 'r' ((:) ' ' ((:) 'n' ((:) 'o'
         ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:)
         'm' ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y'
         ((:) 'e' ((:) 't' ([]))))))))))))))))))))))))))))));
      TEvar _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:)
         ' ' ((:) 't' ((:) 'E' ((:) 'v' ((:) 'a' ((:) 'r' ((:) ' ' ((:) 'n'
         ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:)
         'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' '
         ((:) 'y' ((:) 'e' ((:) 't' ([])))))))))))))))))))))))))))))));
      TSort _ -> ret (unsafeCoerce monad_m) defaultTy;
      TCast t0 _ _ -> denoteType0 t0;
      TProd x t1 t2 ->
       bind (unsafeCoerce monad_m)
         (unsafeCoerce localDenote monad_m reader_m x (denoteType0 t2))
         (\x0 ->
         case x0 of {
          Pair t2' x' ->
           case isKind t1 of {
            GHC.Base.True ->
             bind (unsafeCoerce monad_m) (denoteKind0 t1) (\k ->
               ret (unsafeCoerce monad_m) (TyAll x' k t2'));
            GHC.Base.False ->
             bind (unsafeCoerce monad_m) (denoteType0 t1) (\t1' ->
               ret (unsafeCoerce monad_m) (TyPi x' t1' t2'))}});
      TLambda x kty t0 ->
       bind (unsafeCoerce monad_m)
         (unsafeCoerce localDenote monad_m reader_m x (denoteType0 t0))
         (\x0 ->
         case x0 of {
          Pair t' x' ->
           case isKind kty of {
            GHC.Base.True ->
             bind (unsafeCoerce monad_m) (denoteKind0 kty) (\k ->
               ret (unsafeCoerce monad_m) (TyLamK x' (Some k) t'));
            GHC.Base.False ->
             bind (unsafeCoerce monad_m) (denoteType0 kty) (\ty ->
               ret (unsafeCoerce monad_m) (TyLam x' (Some ty) t'))}});
      TLetIn _ _ _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:)
         ' ' ((:) 't' ((:) 'L' ((:) 'e' ((:) 't' ((:) 'I' ((:) 'n' ((:) ' '
         ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:)
         'l' ((:) 'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd'
         ((:) ' ' ((:) 'y' ((:) 'e' ((:) 't'
         ([]))))))))))))))))))))))))))))))));
      TApp t0 ts ->
       bind (unsafeCoerce monad_m) (denoteType0 t0) (\t' ->
         bind (unsafeCoerce monad_m)
           (list_m (unsafeCoerce monad_m)
             (map (\e ->
               bind (unsafeCoerce monad_m)
                 (unsafeCoerce isType monad_m reader_m either_m e) (\b ->
                 case b of {
                  GHC.Base.True ->
                   fmap (functor_Monad (unsafeCoerce monad_m)) (\x -> Pair
                     GHC.Base.False (Inl x)) (denoteType0 e);
                  GHC.Base.False ->
                   fmap (functor_Monad (unsafeCoerce monad_m)) (\x -> Pair
                     GHC.Base.False (Inr x)) (denoteTerm0 e)})) ts)) (\ts' ->
           ret (unsafeCoerce monad_m) (TyApp t' ts')));
      TConst kern _ ->
       ret (unsafeCoerce monad_m) (TyVar (kername_to_qualid kern));
      TInd ind _ ->
       ret (unsafeCoerce monad_m) (TyVar
         (kername_to_qualid (inductive_mind ind)));
      TConstruct _ _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:)
         ' ' ((:) 't' ((:) 'C' ((:) 'o' ((:) 'n' ((:) 's' ((:) 't' ((:) 'r'
         ((:) 'u' ((:) 'c' ((:) 't' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:)
         ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm' ((:) 'e'
         ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y' ((:) 'e' ((:)
         't' ([]))))))))))))))))))))))))))))))))))));
      TCase _ _ _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:)
         ' ' ((:) 't' ((:) 'C' ((:) 'a' ((:) 's' ((:) 'e' ((:) ' ' ((:) 'n'
         ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:)
         'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' '
         ((:) 'y' ((:) 'e' ((:) 't' ([])))))))))))))))))))))))))))))));
      TProj _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:)
         ' ' ((:) 't' ((:) 'P' ((:) 'r' ((:) 'o' ((:) 'j' ((:) ' ' ((:) 'n'
         ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:)
         'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' '
         ((:) 'y' ((:) 'e' ((:) 't' ([])))))))))))))))))))))))))))))));
      TFix _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:)
         ' ' ((:) 't' ((:) 'F' ((:) 'i' ((:) 'x' ((:) ' ' ((:) 'n' ((:) 'o'
         ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:)
         'm' ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y'
         ((:) 'e' ((:) 't' ([]))))))))))))))))))))))))))))));
      TCoFix _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:)
         ' ' ((:) 't' ((:) 'C' ((:) 'o' ((:) 'F' ((:) 'i' ((:) 'x' ((:) ' '
         ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:)
         'l' ((:) 'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd'
         ((:) ' ' ((:) 'y' ((:) 'e' ((:) 't'
         ([]))))))))))))))))))))))))))))))))};
   denoteTerm0 t =
     case t of {
      TRel n ->
       bind (unsafeCoerce monad_m) (ask (unsafeCoerce reader_m)) (\x ->
         case x of {
          Pair y _ ->
           case y of {
            Pair _ _UU0393_ ->
             bind (unsafeCoerce monad_m)
               (option_m monad_m either_m (nth_error _UU0393_ n)
                 (append ((:) 't' ((:) 'e' ((:) 'r' ((:) 'm' ((:) ' ' ((:)
                   'V' ((:) 'a' ((:) 'r' ((:) 'i' ((:) 'a' ((:) 'b' ((:) 'l'
                   ((:) 'e' ((:) ' ' ([])))))))))))))))
                   (append (string_of_nat n) ((:) ' ' ((:) 'n' ((:) 'o' ((:)
                     't' ((:) ' ' ((:) 'i' ((:) 'n' ((:) ' ' ((:) 'e' ((:)
                     'n' ((:) 'v' ((:) 'i' ((:) 'r' ((:) 'o' ((:) 'n' ((:)
                     'm' ((:) 'e' ((:) 'n' ((:) 't' ([])))))))))))))))))))))))
               (\v -> ret (unsafeCoerce monad_m) (TVar0 v))}});
      TVar _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'V' ((:) 'a' ((:) 'r' ((:)
         ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p'
         ((:) 'l' ((:) 'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:)
         'd' ((:) ' ' ((:) 'y' ((:) 'e' ((:) 't' ([])))))))))))))))))))))))));
      TEvar _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'E' ((:) 'v' ((:) 'a' ((:)
         'r' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm'
         ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:)
         'e' ((:) 'd' ((:) ' ' ((:) 'y' ((:) 'e' ((:) 't'
         ([]))))))))))))))))))))))))));
      TSort _ ->
       ret (unsafeCoerce monad_m) (TVar0 ((:) 't' ((:) 'S' ((:) 'o' ((:) 'r'
         ((:) 't' ([])))))));
      TCast t0 _ _ -> denoteTerm0 t0;
      TProd x kty t0 ->
       bind (unsafeCoerce monad_m)
         (unsafeCoerce localDenote monad_m reader_m x (denoteTerm0 t0))
         (\x0 ->
         case x0 of {
          Pair t' x' ->
           case isKind kty of {
            GHC.Base.True ->
             bind (unsafeCoerce monad_m) (denoteKind0 kty) (\k ->
               ret (unsafeCoerce monad_m) (TLamK x' (Some k) t'));
            GHC.Base.False ->
             bind (unsafeCoerce monad_m) (denoteType0 kty) (\ty ->
               ret (unsafeCoerce monad_m) (TLam x' GHC.Base.False (Some ty)
                 t'))}});
      TLambda x kty t0 ->
       bind (unsafeCoerce monad_m)
         (unsafeCoerce localDenote monad_m reader_m x (denoteTerm0 t0))
         (\x0 ->
         case x0 of {
          Pair t' x' ->
           case isKind kty of {
            GHC.Base.True ->
             bind (unsafeCoerce monad_m) (denoteKind0 kty) (\k ->
               ret (unsafeCoerce monad_m) (TLamK x' (Some k) t'));
            GHC.Base.False ->
             bind (unsafeCoerce monad_m) (denoteType0 kty) (\ty ->
               ret (unsafeCoerce monad_m) (TLam x' GHC.Base.False (Some ty)
                 t'))}});
      TLetIn x t' kty bdy ->
       case is_delta t of {
        GHC.Base.True ->
         bind (unsafeCoerce monad_m) (denoteTerm0 t') (\t'' ->
           case t'' of {
            TApp0 _ l ->
             case l of {
              Nil ->
               ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:) 'e' ((:) 'l'
                 ((:) 'w' ((:) 'r' ((:) 'o' ((:) 'n' ((:) 'g' ([]))))))))));
              Cons p0 l0 ->
               case p0 of {
                Pair b s ->
                 case b of {
                  GHC.Base.True ->
                   ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:) 'e' ((:)
                     'l' ((:) 'w' ((:) 'r' ((:) 'o' ((:) 'n' ((:) 'g'
                     ([]))))))))));
                  GHC.Base.False ->
                   case s of {
                    Inl eqty ->
                     case l0 of {
                      Nil ->
                       ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:) 'e'
                         ((:) 'l' ((:) 'w' ((:) 'r' ((:) 'o' ((:) 'n' ((:)
                         'g' ([]))))))))));
                      Cons p1 l1 ->
                       case p1 of {
                        Pair b0 s0 ->
                         case b0 of {
                          GHC.Base.True ->
                           ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:)
                             'e' ((:) 'l' ((:) 'w' ((:) 'r' ((:) 'o' ((:) 'n'
                             ((:) 'g' ([]))))))))));
                          GHC.Base.False ->
                           case s0 of {
                            Inl _ ->
                             ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:)
                               'e' ((:) 'l' ((:) 'w' ((:) 'r' ((:) 'o' ((:)
                               'n' ((:) 'g' ([]))))))))));
                            Inr x0 ->
                             case l1 of {
                              Nil ->
                               ret (unsafeCoerce monad_m) (TVar0 ((:) 'd'
                                 ((:) 'e' ((:) 'l' ((:) 'w' ((:) 'r' ((:) 'o'
                                 ((:) 'n' ((:) 'g' ([]))))))))));
                              Cons _ l2 ->
                               case l2 of {
                                Nil ->
                                 ret (unsafeCoerce monad_m) (TVar0 ((:) 'd'
                                   ((:) 'e' ((:) 'l' ((:) 'w' ((:) 'r' ((:)
                                   'o' ((:) 'n' ((:) 'g' ([]))))))))));
                                Cons _ l3 ->
                                 case l3 of {
                                  Nil ->
                                   ret (unsafeCoerce monad_m) (TVar0 ((:) 'd'
                                     ((:) 'e' ((:) 'l' ((:) 'w' ((:) 'r' ((:)
                                     'o' ((:) 'n' ((:) 'g' ([]))))))))));
                                  Cons p2 l4 ->
                                   case p2 of {
                                    Pair b1 s1 ->
                                     case b1 of {
                                      GHC.Base.True ->
                                       ret (unsafeCoerce monad_m) (TVar0 ((:)
                                         'd' ((:) 'e' ((:) 'l' ((:) 'w' ((:)
                                         'r' ((:) 'o' ((:) 'n' ((:) 'g'
                                         ([]))))))))));
                                      GHC.Base.False ->
                                       case s1 of {
                                        Inl _ ->
                                         ret (unsafeCoerce monad_m) (TVar0
                                           ((:) 'd' ((:) 'e' ((:) 'l' ((:)
                                           'w' ((:) 'r' ((:) 'o' ((:) 'n'
                                           ((:) 'g' ([]))))))))));
                                        Inr _ ->
                                         case l4 of {
                                          Nil ->
                                           ret (unsafeCoerce monad_m) (TVar0
                                             ((:) 'd' ((:) 'e' ((:) 'l' ((:)
                                             'w' ((:) 'r' ((:) 'o' ((:) 'n'
                                             ((:) 'g' ([]))))))))));
                                          Cons p3 l5 ->
                                           case p3 of {
                                            Pair b2 s2 ->
                                             case b2 of {
                                              GHC.Base.True ->
                                               ret (unsafeCoerce monad_m)
                                                 (TVar0 ((:) 'd' ((:) 'e'
                                                 ((:) 'l' ((:) 'w' ((:) 'r'
                                                 ((:) 'o' ((:) 'n' ((:) 'g'
                                                 ([]))))))))));
                                              GHC.Base.False ->
                                               case s2 of {
                                                Inl _ ->
                                                 ret (unsafeCoerce monad_m)
                                                   (TVar0 ((:) 'd' ((:) 'e'
                                                   ((:) 'l' ((:) 'w' ((:) 'r'
                                                   ((:) 'o' ((:) 'n' ((:) 'g'
                                                   ([]))))))))));
                                                Inr eq ->
                                                 case l5 of {
                                                  Nil ->
                                                   ret (unsafeCoerce monad_m)
                                                     (TDelta
                                                     (eq_elim_term eq eqty
                                                       x0));
                                                  Cons _ _ ->
                                                   ret (unsafeCoerce monad_m)
                                                     (TVar0 ((:) 'd' ((:) 'e'
                                                     ((:) 'l' ((:) 'w' ((:)
                                                     'r' ((:) 'o' ((:) 'n'
                                                     ((:) 'g' ([]))))))))))}}}}}}}}}}}}}}};
                    Inr _ ->
                     ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:) 'e' ((:)
                       'l' ((:) 'w' ((:) 'r' ((:) 'o' ((:) 'n' ((:) 'g'
                       ([]))))))))))}}}};
            _ ->
             ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:) 'e' ((:) 'l'
               ((:) 'w' ((:) 'r' ((:) 'o' ((:) 'n' ((:) 'g' ([]))))))))))});
        GHC.Base.False ->
         bind (unsafeCoerce monad_m)
           (unsafeCoerce localDenote monad_m reader_m x (denoteTerm0 bdy))
           (\x0 ->
           case x0 of {
            Pair bdy' x' ->
             case isKind kty of {
              GHC.Base.True ->
               bind (unsafeCoerce monad_m) (denoteKind0 kty) (\k ->
                 bind (unsafeCoerce monad_m) (denoteType0 t') (\t'' ->
                   ret (unsafeCoerce monad_m) (TLetTy x' k t'' bdy')));
              GHC.Base.False ->
               bind (unsafeCoerce monad_m) (denoteType0 kty) (\ty ->
                 bind (unsafeCoerce monad_m) (denoteTerm0 t') (\t'' ->
                   ret (unsafeCoerce monad_m) (TLetTm x' GHC.Base.False ty
                     t'' bdy')))}})};
      TApp t0 ts ->
       bind (unsafeCoerce monad_m) (denoteTerm0 t0) (\t' ->
         bind (unsafeCoerce monad_m)
           (list_m (unsafeCoerce monad_m)
             (map (\e ->
               bind (unsafeCoerce monad_m)
                 (unsafeCoerce isType monad_m reader_m either_m e) (\b ->
                 case b of {
                  GHC.Base.True ->
                   fmap (functor_Monad (unsafeCoerce monad_m)) (\x -> Inl x)
                     (denoteType0 e);
                  GHC.Base.False ->
                   fmap (functor_Monad (unsafeCoerce monad_m)) (\x -> Inr x)
                     (denoteTerm0 e)})) ts)) (\ts' ->
           bind (unsafeCoerce monad_m)
             (unsafeCoerce reorg_app_args monad_m reader_m t' ts') (\ts'' ->
             ret (unsafeCoerce monad_m) (TApp0 t' ts''))));
      TConst kern _ ->
       ret (unsafeCoerce monad_m) (TVar0 (kername_to_qualid kern));
      TInd ind _ ->
       ret (unsafeCoerce monad_m) (TVar0
         (kername_to_qualid (inductive_mind ind)));
      TConstruct ind n _ ->
       bind (unsafeCoerce monad_m)
         (unsafeCoerce get_ctors monad_m reader_m either_m ind) (\ctors ->
         bind (unsafeCoerce monad_m)
           (option_m monad_m either_m (nth_error ctors n) ((:) 'C' ((:) 'o'
             ((:) 'u' ((:) 'l' ((:) 'd' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't'
             ((:) ' ' ((:) 'f' ((:) 'i' ((:) 'n' ((:) 'd' ((:) ' ' ((:) 'c'
             ((:) 'o' ((:) 'n' ((:) 's' ((:) 't' ((:) 'r' ((:) 'u' ((:) 'c'
             ((:) 't' ((:) 'o' ((:) 'r' ([]))))))))))))))))))))))))))))
           (\x ->
           case x of {
            Pair p0 _ ->
             case p0 of {
              Pair ctor _ -> ret (unsafeCoerce monad_m) (TVar0 ctor)}}));
      TCase ind_and_nbparams mot matchvar brchs ->
       case ind_and_nbparams of {
        Pair ind _ ->
         bind (unsafeCoerce monad_m) (ask (unsafeCoerce reader_m)) (\x ->
           case x of {
            Pair _ renv ->
             case renv of {
              Pair y _ ->
               case y of {
                Pair y0 amots ->
                 case y0 of {
                  Pair y1 anargs ->
                   case y1 of {
                    Pair arargs _ ->
                     bind (unsafeCoerce monad_m)
                       (unsafeCoerce get_ctors monad_m reader_m either_m ind)
                       (\ctors ->
                       bind (unsafeCoerce monad_m) (denoteTerm0 matchvar)
                         (\matchvar' ->
                         bind (unsafeCoerce monad_m) (denoteType0 mot)
                           (\mot' ->
                           bind (unsafeCoerce monad_m)
                             (list_m (unsafeCoerce monad_m)
                               (map
                                 (unsafeCoerce take_args monad_m reader_m
                                   either_m) brchs)) (\args ->
                             bind (unsafeCoerce monad_m)
                               (list_m (unsafeCoerce monad_m)
                                 (map (\pat ->
                                   case pat of {
                                    Pair _ t0 -> denoteTerm0 t0}) brchs))
                               (\brchs_t' ->
                               let {brchs_n = map fst brchs} in
                               let {
                                trimmed_brchs' = map (\pat ->
                                                   case pat of {
                                                    Pair n t0 ->
                                                     removeLambdas n t0})
                                                   (combine brchs_n brchs_t')}
                               in
                               let {
                                constrs = map build_tApp (combine ctors args)}
                               in
                               let {flat_constrs = map flattenTApp constrs}
                               in
                               let {fname = get_rfunc_name matchvar' arargs}
                               in
                               let {mot'0 = get_motive fname amots mot'} in
                               let {app_args = get_nrargs fname anargs} in
                               let {
                                nrargs_brchs = map (bind_nrargs app_args)
                                                 trimmed_brchs'}
                               in
                               let {
                                tapp_args = map (\x0 -> Pair GHC.Base.False
                                              (let {x1 = fst x0} in
                                               Inr (TVar0 x1))) app_args}
                               in
                               let {
                                t' = TApp0 (TMu fname matchvar' (Some mot'0)
                                 (combine flat_constrs nrargs_brchs))
                                 tapp_args}
                               in
                               ret (unsafeCoerce monad_m) (flattenTApp t'))))))}}}}})};
      TProj _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'P' ((:) 'r' ((:) 'o' ((:)
         'j' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm'
         ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:)
         'e' ((:) 'd' ((:) ' ' ((:) 'y' ((:) 'e' ((:) 't'
         ([]))))))))))))))))))))))))));
      TFix mfix _ ->
       case mfix of {
        Nil ->
         raise (unsafeCoerce either_m) ((:) 'M' ((:) 'u' ((:) 't' ((:) 'u'
           ((:) 'a' ((:) 'l' ((:) 'l' ((:) 'y' ((:) ' ' ((:) 'r' ((:) 'e'
           ((:) 'c' ((:) 'u' ((:) 'r' ((:) 's' ((:) 'i' ((:) 'v' ((:) 'e'
           ((:) ' ' ((:) 'f' ((:) 'i' ((:) 'x' ((:) 'p' ((:) 'o' ((:) 'i'
           ((:) 'n' ((:) 't' ((:) 's' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't'
           ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm'
           ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y'
           ((:) 'e' ((:) 't'
           ([])))))))))))))))))))))))))))))))))))))))))))))))));
        Cons f l ->
         case l of {
          Nil ->
           let {fname = get_ident (dname f)} in
           let {body = dbody f} in
           let {type0 = dtype f} in
           let {rarg_pos = rarg f} in
           bind (unsafeCoerce monad_m) (denoteType0 type0) (\ty ->
             bind (unsafeCoerce monad_m)
               (unsafeCoerce denoteMotive monad_m reader_m state_m either_m
                 ty rarg_pos fname) (\renv' ->
               local (unsafeCoerce reader_m) (\pat ->
                 case pat of {
                  Pair y _ ->
                   case y of {
                    Pair genv _UU0393_ -> Pair (Pair genv (Cons fname
                     _UU0393_)) renv'}}) (denoteTerm0 body)));
          Cons _ _ ->
           raise (unsafeCoerce either_m) ((:) 'M' ((:) 'u' ((:) 't' ((:) 'u'
             ((:) 'a' ((:) 'l' ((:) 'l' ((:) 'y' ((:) ' ' ((:) 'r' ((:) 'e'
             ((:) 'c' ((:) 'u' ((:) 'r' ((:) 's' ((:) 'i' ((:) 'v' ((:) 'e'
             ((:) ' ' ((:) 'f' ((:) 'i' ((:) 'x' ((:) 'p' ((:) 'o' ((:) 'i'
             ((:) 'n' ((:) 't' ((:) 's' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't'
             ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm'
             ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y'
             ((:) 'e' ((:) 't'
             ([])))))))))))))))))))))))))))))))))))))))))))))))))}};
      TCoFix _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'C' ((:) 'o' ((:) 'F' ((:)
         'i' ((:) 'x' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i'
         ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:)
         't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y' ((:) 'e' ((:) 't'
         ([])))))))))))))))))))))))))))}}
  in denoteKind0

denoteType :: (Monad (M Any)) -> (MonadReader
              (Prod (Prod Global_env Ctx) Rec_env) (M Any)) -> (MonadState
              Params_env (M Any)) -> (MonadExc Prelude.String (M Any)) ->
              Term -> M Typ
denoteType monad_m reader_m state_m either_m =
  let {
   denoteKind0 t =
     case t of {
      TSort _ -> ret monad_m KdStar;
      TProd x t1 t2 ->
       bind monad_m
         (case isKind t1 of {
           GHC.Base.True ->
            fmap (functor_Monad monad_m) (\x0 -> Inl x0) (denoteKind0 t1);
           GHC.Base.False ->
            fmap (functor_Monad monad_m) (\x0 -> Inr x0)
              (unsafeCoerce denoteType0 t1)}) (\k1 ->
         bind monad_m
           (unsafeCoerce localDenote monad_m reader_m x (denoteKind0 t2))
           (\x0 -> case x0 of {
                    Pair k2 x' -> ret monad_m (KdAll x' k1 k2)}));
      _ ->
       raise either_m ((:) 'I' ((:) 'l' ((:) 'l' ((:) '-' ((:) 'f' ((:) 'o'
         ((:) 'r' ((:) 'm' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'k' ((:) 'i' ((:)
         'n' ((:) 'd' ([]))))))))))))))))};
   denoteType0 t =
     case t of {
      TRel n ->
       bind (unsafeCoerce monad_m) (ask (unsafeCoerce reader_m)) (\x ->
         case x of {
          Pair y _ ->
           case y of {
            Pair _ _UU0393_ ->
             bind (unsafeCoerce monad_m)
               (option_m monad_m either_m
                 (nth_error (unsafeCoerce _UU0393_) n)
                 (append ((:) 't' ((:) 'y' ((:) ' ' ((:) 't' ((:) 'R' ((:)
                   'e' ((:) 'l' ((:) ' ' ([])))))))))
                   (append (string_of_nat n)
                     (append ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' '
                       ((:) 'i' ((:) 'n' ((:) ' ' ((:) 'e' ((:) 'n' ((:) 'v'
                       ((:) 'i' ((:) 'r' ((:) 'o' ((:) 'n' ((:) 'm' ((:) 'e'
                       ((:) 'n' ((:) 't' ((:) ' ' ([])))))))))))))))))))))
                       (showList _UU0393_))))) (\v ->
               ret (unsafeCoerce monad_m) (TyVar v))}});
      TVar _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:)
         ' ' ((:) 't' ((:) 'V' ((:) 'a' ((:) 'r' ((:) ' ' ((:) 'n' ((:) 'o'
         ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:)
         'm' ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y'
         ((:) 'e' ((:) 't' ([]))))))))))))))))))))))))))))));
      TEvar _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:)
         ' ' ((:) 't' ((:) 'E' ((:) 'v' ((:) 'a' ((:) 'r' ((:) ' ' ((:) 'n'
         ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:)
         'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' '
         ((:) 'y' ((:) 'e' ((:) 't' ([])))))))))))))))))))))))))))))));
      TSort _ -> ret (unsafeCoerce monad_m) defaultTy;
      TCast t0 _ _ -> denoteType0 t0;
      TProd x t1 t2 ->
       bind (unsafeCoerce monad_m)
         (unsafeCoerce localDenote monad_m reader_m x (denoteType0 t2))
         (\x0 ->
         case x0 of {
          Pair t2' x' ->
           case isKind t1 of {
            GHC.Base.True ->
             bind (unsafeCoerce monad_m) (unsafeCoerce denoteKind0 t1) (\k ->
               ret (unsafeCoerce monad_m) (TyAll x' k t2'));
            GHC.Base.False ->
             bind (unsafeCoerce monad_m) (denoteType0 t1) (\t1' ->
               ret (unsafeCoerce monad_m) (TyPi x' t1' t2'))}});
      TLambda x kty t0 ->
       bind (unsafeCoerce monad_m)
         (unsafeCoerce localDenote monad_m reader_m x (denoteType0 t0))
         (\x0 ->
         case x0 of {
          Pair t' x' ->
           case isKind kty of {
            GHC.Base.True ->
             bind (unsafeCoerce monad_m) (unsafeCoerce denoteKind0 kty)
               (\k -> ret (unsafeCoerce monad_m) (TyLamK x' (Some k) t'));
            GHC.Base.False ->
             bind (unsafeCoerce monad_m) (denoteType0 kty) (\ty ->
               ret (unsafeCoerce monad_m) (TyLam x' (Some ty) t'))}});
      TLetIn _ _ _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:)
         ' ' ((:) 't' ((:) 'L' ((:) 'e' ((:) 't' ((:) 'I' ((:) 'n' ((:) ' '
         ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:)
         'l' ((:) 'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd'
         ((:) ' ' ((:) 'y' ((:) 'e' ((:) 't'
         ([]))))))))))))))))))))))))))))))));
      TApp t0 ts ->
       bind (unsafeCoerce monad_m) (denoteType0 t0) (\t' ->
         bind (unsafeCoerce monad_m)
           (list_m (unsafeCoerce monad_m)
             (map (\e ->
               bind (unsafeCoerce monad_m)
                 (unsafeCoerce isType monad_m reader_m either_m e) (\b ->
                 case b of {
                  GHC.Base.True ->
                   fmap (functor_Monad (unsafeCoerce monad_m)) (\x -> Pair
                     GHC.Base.False (Inl x)) (denoteType0 e);
                  GHC.Base.False ->
                   fmap (functor_Monad (unsafeCoerce monad_m)) (\x -> Pair
                     GHC.Base.False (Inr x)) (denoteTerm0 e)})) ts)) (\ts' ->
           ret (unsafeCoerce monad_m) (TyApp t' ts')));
      TConst kern _ ->
       ret (unsafeCoerce monad_m) (TyVar (kername_to_qualid kern));
      TInd ind _ ->
       ret (unsafeCoerce monad_m) (TyVar
         (kername_to_qualid (inductive_mind ind)));
      TConstruct _ _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:)
         ' ' ((:) 't' ((:) 'C' ((:) 'o' ((:) 'n' ((:) 's' ((:) 't' ((:) 'r'
         ((:) 'u' ((:) 'c' ((:) 't' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:)
         ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm' ((:) 'e'
         ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y' ((:) 'e' ((:)
         't' ([]))))))))))))))))))))))))))))))))))));
      TCase _ _ _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:)
         ' ' ((:) 't' ((:) 'C' ((:) 'a' ((:) 's' ((:) 'e' ((:) ' ' ((:) 'n'
         ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:)
         'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' '
         ((:) 'y' ((:) 'e' ((:) 't' ([])))))))))))))))))))))))))))))));
      TProj _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:)
         ' ' ((:) 't' ((:) 'P' ((:) 'r' ((:) 'o' ((:) 'j' ((:) ' ' ((:) 'n'
         ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:)
         'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' '
         ((:) 'y' ((:) 'e' ((:) 't' ([])))))))))))))))))))))))))))))));
      TFix _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:)
         ' ' ((:) 't' ((:) 'F' ((:) 'i' ((:) 'x' ((:) ' ' ((:) 'n' ((:) 'o'
         ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:)
         'm' ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y'
         ((:) 'e' ((:) 't' ([]))))))))))))))))))))))))))))));
      TCoFix _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:)
         ' ' ((:) 't' ((:) 'C' ((:) 'o' ((:) 'F' ((:) 'i' ((:) 'x' ((:) ' '
         ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:)
         'l' ((:) 'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd'
         ((:) ' ' ((:) 'y' ((:) 'e' ((:) 't'
         ([]))))))))))))))))))))))))))))))))};
   denoteTerm0 t =
     case t of {
      TRel n ->
       bind (unsafeCoerce monad_m) (ask (unsafeCoerce reader_m)) (\x ->
         case x of {
          Pair y _ ->
           case y of {
            Pair _ _UU0393_ ->
             bind (unsafeCoerce monad_m)
               (option_m monad_m either_m (nth_error _UU0393_ n)
                 (append ((:) 't' ((:) 'e' ((:) 'r' ((:) 'm' ((:) ' ' ((:)
                   'V' ((:) 'a' ((:) 'r' ((:) 'i' ((:) 'a' ((:) 'b' ((:) 'l'
                   ((:) 'e' ((:) ' ' ([])))))))))))))))
                   (append (string_of_nat n) ((:) ' ' ((:) 'n' ((:) 'o' ((:)
                     't' ((:) ' ' ((:) 'i' ((:) 'n' ((:) ' ' ((:) 'e' ((:)
                     'n' ((:) 'v' ((:) 'i' ((:) 'r' ((:) 'o' ((:) 'n' ((:)
                     'm' ((:) 'e' ((:) 'n' ((:) 't' ([])))))))))))))))))))))))
               (\v -> ret (unsafeCoerce monad_m) (TVar0 v))}});
      TVar _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'V' ((:) 'a' ((:) 'r' ((:)
         ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p'
         ((:) 'l' ((:) 'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:)
         'd' ((:) ' ' ((:) 'y' ((:) 'e' ((:) 't' ([])))))))))))))))))))))))));
      TEvar _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'E' ((:) 'v' ((:) 'a' ((:)
         'r' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm'
         ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:)
         'e' ((:) 'd' ((:) ' ' ((:) 'y' ((:) 'e' ((:) 't'
         ([]))))))))))))))))))))))))));
      TSort _ ->
       ret (unsafeCoerce monad_m) (TVar0 ((:) 't' ((:) 'S' ((:) 'o' ((:) 'r'
         ((:) 't' ([])))))));
      TCast t0 _ _ -> denoteTerm0 t0;
      TProd x kty t0 ->
       bind (unsafeCoerce monad_m)
         (unsafeCoerce localDenote monad_m reader_m x (denoteTerm0 t0))
         (\x0 ->
         case x0 of {
          Pair t' x' ->
           case isKind kty of {
            GHC.Base.True ->
             bind (unsafeCoerce monad_m) (unsafeCoerce denoteKind0 kty)
               (\k -> ret (unsafeCoerce monad_m) (TLamK x' (Some k) t'));
            GHC.Base.False ->
             bind (unsafeCoerce monad_m) (denoteType0 kty) (\ty ->
               ret (unsafeCoerce monad_m) (TLam x' GHC.Base.False (Some ty)
                 t'))}});
      TLambda x kty t0 ->
       bind (unsafeCoerce monad_m)
         (unsafeCoerce localDenote monad_m reader_m x (denoteTerm0 t0))
         (\x0 ->
         case x0 of {
          Pair t' x' ->
           case isKind kty of {
            GHC.Base.True ->
             bind (unsafeCoerce monad_m) (unsafeCoerce denoteKind0 kty)
               (\k -> ret (unsafeCoerce monad_m) (TLamK x' (Some k) t'));
            GHC.Base.False ->
             bind (unsafeCoerce monad_m) (denoteType0 kty) (\ty ->
               ret (unsafeCoerce monad_m) (TLam x' GHC.Base.False (Some ty)
                 t'))}});
      TLetIn x t' kty bdy ->
       case is_delta t of {
        GHC.Base.True ->
         bind (unsafeCoerce monad_m) (denoteTerm0 t') (\t'' ->
           case t'' of {
            TApp0 _ l ->
             case l of {
              Nil ->
               ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:) 'e' ((:) 'l'
                 ((:) 'w' ((:) 'r' ((:) 'o' ((:) 'n' ((:) 'g' ([]))))))))));
              Cons p0 l0 ->
               case p0 of {
                Pair b s ->
                 case b of {
                  GHC.Base.True ->
                   ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:) 'e' ((:)
                     'l' ((:) 'w' ((:) 'r' ((:) 'o' ((:) 'n' ((:) 'g'
                     ([]))))))))));
                  GHC.Base.False ->
                   case s of {
                    Inl eqty ->
                     case l0 of {
                      Nil ->
                       ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:) 'e'
                         ((:) 'l' ((:) 'w' ((:) 'r' ((:) 'o' ((:) 'n' ((:)
                         'g' ([]))))))))));
                      Cons p1 l1 ->
                       case p1 of {
                        Pair b0 s0 ->
                         case b0 of {
                          GHC.Base.True ->
                           ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:)
                             'e' ((:) 'l' ((:) 'w' ((:) 'r' ((:) 'o' ((:) 'n'
                             ((:) 'g' ([]))))))))));
                          GHC.Base.False ->
                           case s0 of {
                            Inl _ ->
                             ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:)
                               'e' ((:) 'l' ((:) 'w' ((:) 'r' ((:) 'o' ((:)
                               'n' ((:) 'g' ([]))))))))));
                            Inr x0 ->
                             case l1 of {
                              Nil ->
                               ret (unsafeCoerce monad_m) (TVar0 ((:) 'd'
                                 ((:) 'e' ((:) 'l' ((:) 'w' ((:) 'r' ((:) 'o'
                                 ((:) 'n' ((:) 'g' ([]))))))))));
                              Cons _ l2 ->
                               case l2 of {
                                Nil ->
                                 ret (unsafeCoerce monad_m) (TVar0 ((:) 'd'
                                   ((:) 'e' ((:) 'l' ((:) 'w' ((:) 'r' ((:)
                                   'o' ((:) 'n' ((:) 'g' ([]))))))))));
                                Cons _ l3 ->
                                 case l3 of {
                                  Nil ->
                                   ret (unsafeCoerce monad_m) (TVar0 ((:) 'd'
                                     ((:) 'e' ((:) 'l' ((:) 'w' ((:) 'r' ((:)
                                     'o' ((:) 'n' ((:) 'g' ([]))))))))));
                                  Cons p2 l4 ->
                                   case p2 of {
                                    Pair b1 s1 ->
                                     case b1 of {
                                      GHC.Base.True ->
                                       ret (unsafeCoerce monad_m) (TVar0 ((:)
                                         'd' ((:) 'e' ((:) 'l' ((:) 'w' ((:)
                                         'r' ((:) 'o' ((:) 'n' ((:) 'g'
                                         ([]))))))))));
                                      GHC.Base.False ->
                                       case s1 of {
                                        Inl _ ->
                                         ret (unsafeCoerce monad_m) (TVar0
                                           ((:) 'd' ((:) 'e' ((:) 'l' ((:)
                                           'w' ((:) 'r' ((:) 'o' ((:) 'n'
                                           ((:) 'g' ([]))))))))));
                                        Inr _ ->
                                         case l4 of {
                                          Nil ->
                                           ret (unsafeCoerce monad_m) (TVar0
                                             ((:) 'd' ((:) 'e' ((:) 'l' ((:)
                                             'w' ((:) 'r' ((:) 'o' ((:) 'n'
                                             ((:) 'g' ([]))))))))));
                                          Cons p3 l5 ->
                                           case p3 of {
                                            Pair b2 s2 ->
                                             case b2 of {
                                              GHC.Base.True ->
                                               ret (unsafeCoerce monad_m)
                                                 (TVar0 ((:) 'd' ((:) 'e'
                                                 ((:) 'l' ((:) 'w' ((:) 'r'
                                                 ((:) 'o' ((:) 'n' ((:) 'g'
                                                 ([]))))))))));
                                              GHC.Base.False ->
                                               case s2 of {
                                                Inl _ ->
                                                 ret (unsafeCoerce monad_m)
                                                   (TVar0 ((:) 'd' ((:) 'e'
                                                   ((:) 'l' ((:) 'w' ((:) 'r'
                                                   ((:) 'o' ((:) 'n' ((:) 'g'
                                                   ([]))))))))));
                                                Inr eq ->
                                                 case l5 of {
                                                  Nil ->
                                                   ret (unsafeCoerce monad_m)
                                                     (TDelta
                                                     (eq_elim_term eq eqty
                                                       x0));
                                                  Cons _ _ ->
                                                   ret (unsafeCoerce monad_m)
                                                     (TVar0 ((:) 'd' ((:) 'e'
                                                     ((:) 'l' ((:) 'w' ((:)
                                                     'r' ((:) 'o' ((:) 'n'
                                                     ((:) 'g' ([]))))))))))}}}}}}}}}}}}}}};
                    Inr _ ->
                     ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:) 'e' ((:)
                       'l' ((:) 'w' ((:) 'r' ((:) 'o' ((:) 'n' ((:) 'g'
                       ([]))))))))))}}}};
            _ ->
             ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:) 'e' ((:) 'l'
               ((:) 'w' ((:) 'r' ((:) 'o' ((:) 'n' ((:) 'g' ([]))))))))))});
        GHC.Base.False ->
         bind (unsafeCoerce monad_m)
           (unsafeCoerce localDenote monad_m reader_m x (denoteTerm0 bdy))
           (\x0 ->
           case x0 of {
            Pair bdy' x' ->
             case isKind kty of {
              GHC.Base.True ->
               bind (unsafeCoerce monad_m) (unsafeCoerce denoteKind0 kty)
                 (\k ->
                 bind (unsafeCoerce monad_m) (denoteType0 t') (\t'' ->
                   ret (unsafeCoerce monad_m) (TLetTy x' k t'' bdy')));
              GHC.Base.False ->
               bind (unsafeCoerce monad_m) (denoteType0 kty) (\ty ->
                 bind (unsafeCoerce monad_m) (denoteTerm0 t') (\t'' ->
                   ret (unsafeCoerce monad_m) (TLetTm x' GHC.Base.False ty
                     t'' bdy')))}})};
      TApp t0 ts ->
       bind (unsafeCoerce monad_m) (denoteTerm0 t0) (\t' ->
         bind (unsafeCoerce monad_m)
           (list_m (unsafeCoerce monad_m)
             (map (\e ->
               bind (unsafeCoerce monad_m)
                 (unsafeCoerce isType monad_m reader_m either_m e) (\b ->
                 case b of {
                  GHC.Base.True ->
                   fmap (functor_Monad (unsafeCoerce monad_m)) (\x -> Inl x)
                     (denoteType0 e);
                  GHC.Base.False ->
                   fmap (functor_Monad (unsafeCoerce monad_m)) (\x -> Inr x)
                     (denoteTerm0 e)})) ts)) (\ts' ->
           bind (unsafeCoerce monad_m)
             (unsafeCoerce reorg_app_args monad_m reader_m t' ts') (\ts'' ->
             ret (unsafeCoerce monad_m) (TApp0 t' ts''))));
      TConst kern _ ->
       ret (unsafeCoerce monad_m) (TVar0 (kername_to_qualid kern));
      TInd ind _ ->
       ret (unsafeCoerce monad_m) (TVar0
         (kername_to_qualid (inductive_mind ind)));
      TConstruct ind n _ ->
       bind (unsafeCoerce monad_m)
         (unsafeCoerce get_ctors monad_m reader_m either_m ind) (\ctors ->
         bind (unsafeCoerce monad_m)
           (option_m monad_m either_m (nth_error ctors n) ((:) 'C' ((:) 'o'
             ((:) 'u' ((:) 'l' ((:) 'd' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't'
             ((:) ' ' ((:) 'f' ((:) 'i' ((:) 'n' ((:) 'd' ((:) ' ' ((:) 'c'
             ((:) 'o' ((:) 'n' ((:) 's' ((:) 't' ((:) 'r' ((:) 'u' ((:) 'c'
             ((:) 't' ((:) 'o' ((:) 'r' ([]))))))))))))))))))))))))))))
           (\x ->
           case x of {
            Pair p0 _ ->
             case p0 of {
              Pair ctor _ -> ret (unsafeCoerce monad_m) (TVar0 ctor)}}));
      TCase ind_and_nbparams mot matchvar brchs ->
       case ind_and_nbparams of {
        Pair ind _ ->
         bind (unsafeCoerce monad_m) (ask (unsafeCoerce reader_m)) (\x ->
           case x of {
            Pair _ renv ->
             case renv of {
              Pair y _ ->
               case y of {
                Pair y0 amots ->
                 case y0 of {
                  Pair y1 anargs ->
                   case y1 of {
                    Pair arargs _ ->
                     bind (unsafeCoerce monad_m)
                       (unsafeCoerce get_ctors monad_m reader_m either_m ind)
                       (\ctors ->
                       bind (unsafeCoerce monad_m) (denoteTerm0 matchvar)
                         (\matchvar' ->
                         bind (unsafeCoerce monad_m) (denoteType0 mot)
                           (\mot' ->
                           bind (unsafeCoerce monad_m)
                             (list_m (unsafeCoerce monad_m)
                               (map
                                 (unsafeCoerce take_args monad_m reader_m
                                   either_m) brchs)) (\args ->
                             bind (unsafeCoerce monad_m)
                               (list_m (unsafeCoerce monad_m)
                                 (map (\pat ->
                                   case pat of {
                                    Pair _ t0 -> denoteTerm0 t0}) brchs))
                               (\brchs_t' ->
                               let {brchs_n = map fst brchs} in
                               let {
                                trimmed_brchs' = map (\pat ->
                                                   case pat of {
                                                    Pair n t0 ->
                                                     removeLambdas n t0})
                                                   (combine brchs_n brchs_t')}
                               in
                               let {
                                constrs = map build_tApp (combine ctors args)}
                               in
                               let {flat_constrs = map flattenTApp constrs}
                               in
                               let {fname = get_rfunc_name matchvar' arargs}
                               in
                               let {mot'0 = get_motive fname amots mot'} in
                               let {app_args = get_nrargs fname anargs} in
                               let {
                                nrargs_brchs = map (bind_nrargs app_args)
                                                 trimmed_brchs'}
                               in
                               let {
                                tapp_args = map (\x0 -> Pair GHC.Base.False
                                              (let {x1 = fst x0} in
                                               Inr (TVar0 x1))) app_args}
                               in
                               let {
                                t' = TApp0 (TMu fname matchvar' (Some mot'0)
                                 (combine flat_constrs nrargs_brchs))
                                 tapp_args}
                               in
                               ret (unsafeCoerce monad_m) (flattenTApp t'))))))}}}}})};
      TProj _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'P' ((:) 'r' ((:) 'o' ((:)
         'j' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm'
         ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:)
         'e' ((:) 'd' ((:) ' ' ((:) 'y' ((:) 'e' ((:) 't'
         ([]))))))))))))))))))))))))));
      TFix mfix _ ->
       case mfix of {
        Nil ->
         raise (unsafeCoerce either_m) ((:) 'M' ((:) 'u' ((:) 't' ((:) 'u'
           ((:) 'a' ((:) 'l' ((:) 'l' ((:) 'y' ((:) ' ' ((:) 'r' ((:) 'e'
           ((:) 'c' ((:) 'u' ((:) 'r' ((:) 's' ((:) 'i' ((:) 'v' ((:) 'e'
           ((:) ' ' ((:) 'f' ((:) 'i' ((:) 'x' ((:) 'p' ((:) 'o' ((:) 'i'
           ((:) 'n' ((:) 't' ((:) 's' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't'
           ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm'
           ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y'
           ((:) 'e' ((:) 't'
           ([])))))))))))))))))))))))))))))))))))))))))))))))));
        Cons f l ->
         case l of {
          Nil ->
           let {fname = get_ident (dname f)} in
           let {body = dbody f} in
           let {type0 = dtype f} in
           let {rarg_pos = rarg f} in
           bind (unsafeCoerce monad_m) (denoteType0 type0) (\ty ->
             bind (unsafeCoerce monad_m)
               (unsafeCoerce denoteMotive monad_m reader_m state_m either_m
                 ty rarg_pos fname) (\renv' ->
               local (unsafeCoerce reader_m) (\pat ->
                 case pat of {
                  Pair y _ ->
                   case y of {
                    Pair genv _UU0393_ -> Pair (Pair genv (Cons fname
                     _UU0393_)) renv'}}) (denoteTerm0 body)));
          Cons _ _ ->
           raise (unsafeCoerce either_m) ((:) 'M' ((:) 'u' ((:) 't' ((:) 'u'
             ((:) 'a' ((:) 'l' ((:) 'l' ((:) 'y' ((:) ' ' ((:) 'r' ((:) 'e'
             ((:) 'c' ((:) 'u' ((:) 'r' ((:) 's' ((:) 'i' ((:) 'v' ((:) 'e'
             ((:) ' ' ((:) 'f' ((:) 'i' ((:) 'x' ((:) 'p' ((:) 'o' ((:) 'i'
             ((:) 'n' ((:) 't' ((:) 's' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't'
             ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm'
             ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y'
             ((:) 'e' ((:) 't'
             ([])))))))))))))))))))))))))))))))))))))))))))))))))}};
      TCoFix _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'C' ((:) 'o' ((:) 'F' ((:)
         'i' ((:) 'x' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i'
         ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:)
         't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y' ((:) 'e' ((:) 't'
         ([])))))))))))))))))))))))))))}}
  in denoteType0

denoteTerm :: (Monad (M Any)) -> (MonadReader
              (Prod (Prod Global_env Ctx) Rec_env) (M Any)) -> (MonadState
              Params_env (M Any)) -> (MonadExc Prelude.String (M Any)) ->
              Term -> M Term0
denoteTerm monad_m reader_m state_m either_m =
  let {
   denoteKind0 t =
     case t of {
      TSort _ -> ret monad_m KdStar;
      TProd x t1 t2 ->
       bind monad_m
         (case isKind t1 of {
           GHC.Base.True ->
            fmap (functor_Monad monad_m) (\x0 -> Inl x0) (denoteKind0 t1);
           GHC.Base.False ->
            fmap (functor_Monad monad_m) (\x0 -> Inr x0) (denoteType0 t1)})
         (\k1 ->
         bind monad_m
           (unsafeCoerce localDenote monad_m reader_m x (denoteKind0 t2))
           (\x0 -> case x0 of {
                    Pair k2 x' -> ret monad_m (KdAll x' k1 k2)}));
      _ ->
       raise either_m ((:) 'I' ((:) 'l' ((:) 'l' ((:) '-' ((:) 'f' ((:) 'o'
         ((:) 'r' ((:) 'm' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'k' ((:) 'i' ((:)
         'n' ((:) 'd' ([]))))))))))))))))};
   denoteType0 t =
     case t of {
      TRel n ->
       bind monad_m (ask reader_m) (\x ->
         case x of {
          Pair y _ ->
           case y of {
            Pair _ _UU0393_ ->
             bind monad_m
               (option_m monad_m either_m
                 (nth_error (unsafeCoerce _UU0393_) n)
                 (append ((:) 't' ((:) 'y' ((:) ' ' ((:) 't' ((:) 'R' ((:)
                   'e' ((:) 'l' ((:) ' ' ([])))))))))
                   (append (string_of_nat n)
                     (append ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' '
                       ((:) 'i' ((:) 'n' ((:) ' ' ((:) 'e' ((:) 'n' ((:) 'v'
                       ((:) 'i' ((:) 'r' ((:) 'o' ((:) 'n' ((:) 'm' ((:) 'e'
                       ((:) 'n' ((:) 't' ((:) ' ' ([])))))))))))))))))))))
                       (showList _UU0393_))))) (\v -> ret monad_m (TyVar v))}});
      TVar _ ->
       raise either_m ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:) ' ' ((:) 't'
         ((:) 'V' ((:) 'a' ((:) 'r' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:)
         ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm' ((:) 'e'
         ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y' ((:) 'e' ((:)
         't' ([]))))))))))))))))))))))))))))));
      TEvar _ _ ->
       raise either_m ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:) ' ' ((:) 't'
         ((:) 'E' ((:) 'v' ((:) 'a' ((:) 'r' ((:) ' ' ((:) 'n' ((:) 'o' ((:)
         't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm'
         ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y' ((:)
         'e' ((:) 't' ([])))))))))))))))))))))))))))))));
      TSort _ -> ret monad_m defaultTy;
      TCast t0 _ _ -> denoteType0 t0;
      TProd x t1 t2 ->
       bind monad_m
         (unsafeCoerce localDenote monad_m reader_m x (denoteType0 t2))
         (\x0 ->
         case x0 of {
          Pair t2' x' ->
           case isKind t1 of {
            GHC.Base.True ->
             bind monad_m (denoteKind0 t1) (\k ->
               ret monad_m (TyAll x' k t2'));
            GHC.Base.False ->
             bind monad_m (denoteType0 t1) (\t1' ->
               ret monad_m (TyPi x' t1' t2'))}});
      TLambda x kty t0 ->
       bind monad_m
         (unsafeCoerce localDenote monad_m reader_m x (denoteType0 t0))
         (\x0 ->
         case x0 of {
          Pair t' x' ->
           case isKind kty of {
            GHC.Base.True ->
             bind monad_m (denoteKind0 kty) (\k ->
               ret monad_m (TyLamK x' (Some k) t'));
            GHC.Base.False ->
             bind monad_m (denoteType0 kty) (\ty ->
               ret monad_m (TyLam x' (Some ty) t'))}});
      TLetIn _ _ _ _ ->
       raise either_m ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:) ' ' ((:) 't'
         ((:) 'L' ((:) 'e' ((:) 't' ((:) 'I' ((:) 'n' ((:) ' ' ((:) 'n' ((:)
         'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e'
         ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' ' ((:)
         'y' ((:) 'e' ((:) 't' ([]))))))))))))))))))))))))))))))));
      TApp t0 ts ->
       bind monad_m (denoteType0 t0) (\t' ->
         bind monad_m
           (list_m monad_m
             (map (\e ->
               bind monad_m (unsafeCoerce isType monad_m reader_m either_m e)
                 (\b ->
                 case b of {
                  GHC.Base.True ->
                   fmap (functor_Monad monad_m) (\x -> Pair GHC.Base.False
                     (Inl x)) (denoteType0 e);
                  GHC.Base.False ->
                   fmap (functor_Monad monad_m) (\x -> Pair GHC.Base.False
                     (Inr x)) (unsafeCoerce denoteTerm0 e)})) ts)) (\ts' ->
           ret monad_m (TyApp t' ts')));
      TConst kern _ -> ret monad_m (TyVar (kername_to_qualid kern));
      TInd ind _ ->
       ret monad_m (TyVar (kername_to_qualid (inductive_mind ind)));
      TConstruct _ _ _ ->
       raise either_m ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:) ' ' ((:) 't'
         ((:) 'C' ((:) 'o' ((:) 'n' ((:) 's' ((:) 't' ((:) 'r' ((:) 'u' ((:)
         'c' ((:) 't' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i'
         ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:)
         't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y' ((:) 'e' ((:) 't'
         ([]))))))))))))))))))))))))))))))))))));
      TCase _ _ _ _ ->
       raise either_m ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:) ' ' ((:) 't'
         ((:) 'C' ((:) 'a' ((:) 's' ((:) 'e' ((:) ' ' ((:) 'n' ((:) 'o' ((:)
         't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm'
         ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y' ((:)
         'e' ((:) 't' ([])))))))))))))))))))))))))))))));
      TProj _ _ ->
       raise either_m ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:) ' ' ((:) 't'
         ((:) 'P' ((:) 'r' ((:) 'o' ((:) 'j' ((:) ' ' ((:) 'n' ((:) 'o' ((:)
         't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm'
         ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y' ((:)
         'e' ((:) 't' ([])))))))))))))))))))))))))))))));
      TFix _ _ ->
       raise either_m ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:) ' ' ((:) 't'
         ((:) 'F' ((:) 'i' ((:) 'x' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:)
         ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm' ((:) 'e'
         ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y' ((:) 'e' ((:)
         't' ([]))))))))))))))))))))))))))))));
      TCoFix _ _ ->
       raise either_m ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:) ' ' ((:) 't'
         ((:) 'C' ((:) 'o' ((:) 'F' ((:) 'i' ((:) 'x' ((:) ' ' ((:) 'n' ((:)
         'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e'
         ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' ' ((:)
         'y' ((:) 'e' ((:) 't' ([]))))))))))))))))))))))))))))))))};
   denoteTerm0 t =
     case t of {
      TRel n ->
       bind (unsafeCoerce monad_m) (ask (unsafeCoerce reader_m)) (\x ->
         case x of {
          Pair y _ ->
           case y of {
            Pair _ _UU0393_ ->
             bind (unsafeCoerce monad_m)
               (option_m monad_m either_m (nth_error _UU0393_ n)
                 (append ((:) 't' ((:) 'e' ((:) 'r' ((:) 'm' ((:) ' ' ((:)
                   'V' ((:) 'a' ((:) 'r' ((:) 'i' ((:) 'a' ((:) 'b' ((:) 'l'
                   ((:) 'e' ((:) ' ' ([])))))))))))))))
                   (append (string_of_nat n) ((:) ' ' ((:) 'n' ((:) 'o' ((:)
                     't' ((:) ' ' ((:) 'i' ((:) 'n' ((:) ' ' ((:) 'e' ((:)
                     'n' ((:) 'v' ((:) 'i' ((:) 'r' ((:) 'o' ((:) 'n' ((:)
                     'm' ((:) 'e' ((:) 'n' ((:) 't' ([])))))))))))))))))))))))
               (\v -> ret (unsafeCoerce monad_m) (TVar0 v))}});
      TVar _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'V' ((:) 'a' ((:) 'r' ((:)
         ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p'
         ((:) 'l' ((:) 'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:)
         'd' ((:) ' ' ((:) 'y' ((:) 'e' ((:) 't' ([])))))))))))))))))))))))));
      TEvar _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'E' ((:) 'v' ((:) 'a' ((:)
         'r' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm'
         ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:)
         'e' ((:) 'd' ((:) ' ' ((:) 'y' ((:) 'e' ((:) 't'
         ([]))))))))))))))))))))))))));
      TSort _ ->
       ret (unsafeCoerce monad_m) (TVar0 ((:) 't' ((:) 'S' ((:) 'o' ((:) 'r'
         ((:) 't' ([])))))));
      TCast t0 _ _ -> denoteTerm0 t0;
      TProd x kty t0 ->
       bind (unsafeCoerce monad_m)
         (unsafeCoerce localDenote monad_m reader_m x (denoteTerm0 t0))
         (\x0 ->
         case x0 of {
          Pair t' x' ->
           case isKind kty of {
            GHC.Base.True ->
             bind (unsafeCoerce monad_m) (unsafeCoerce denoteKind0 kty)
               (\k -> ret (unsafeCoerce monad_m) (TLamK x' (Some k) t'));
            GHC.Base.False ->
             bind (unsafeCoerce monad_m) (unsafeCoerce denoteType0 kty)
               (\ty ->
               ret (unsafeCoerce monad_m) (TLam x' GHC.Base.False (Some ty)
                 t'))}});
      TLambda x kty t0 ->
       bind (unsafeCoerce monad_m)
         (unsafeCoerce localDenote monad_m reader_m x (denoteTerm0 t0))
         (\x0 ->
         case x0 of {
          Pair t' x' ->
           case isKind kty of {
            GHC.Base.True ->
             bind (unsafeCoerce monad_m) (unsafeCoerce denoteKind0 kty)
               (\k -> ret (unsafeCoerce monad_m) (TLamK x' (Some k) t'));
            GHC.Base.False ->
             bind (unsafeCoerce monad_m) (unsafeCoerce denoteType0 kty)
               (\ty ->
               ret (unsafeCoerce monad_m) (TLam x' GHC.Base.False (Some ty)
                 t'))}});
      TLetIn x t' kty bdy ->
       case is_delta t of {
        GHC.Base.True ->
         bind (unsafeCoerce monad_m) (denoteTerm0 t') (\t'' ->
           case t'' of {
            TApp0 _ l ->
             case l of {
              Nil ->
               ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:) 'e' ((:) 'l'
                 ((:) 'w' ((:) 'r' ((:) 'o' ((:) 'n' ((:) 'g' ([]))))))))));
              Cons p0 l0 ->
               case p0 of {
                Pair b s ->
                 case b of {
                  GHC.Base.True ->
                   ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:) 'e' ((:)
                     'l' ((:) 'w' ((:) 'r' ((:) 'o' ((:) 'n' ((:) 'g'
                     ([]))))))))));
                  GHC.Base.False ->
                   case s of {
                    Inl eqty ->
                     case l0 of {
                      Nil ->
                       ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:) 'e'
                         ((:) 'l' ((:) 'w' ((:) 'r' ((:) 'o' ((:) 'n' ((:)
                         'g' ([]))))))))));
                      Cons p1 l1 ->
                       case p1 of {
                        Pair b0 s0 ->
                         case b0 of {
                          GHC.Base.True ->
                           ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:)
                             'e' ((:) 'l' ((:) 'w' ((:) 'r' ((:) 'o' ((:) 'n'
                             ((:) 'g' ([]))))))))));
                          GHC.Base.False ->
                           case s0 of {
                            Inl _ ->
                             ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:)
                               'e' ((:) 'l' ((:) 'w' ((:) 'r' ((:) 'o' ((:)
                               'n' ((:) 'g' ([]))))))))));
                            Inr x0 ->
                             case l1 of {
                              Nil ->
                               ret (unsafeCoerce monad_m) (TVar0 ((:) 'd'
                                 ((:) 'e' ((:) 'l' ((:) 'w' ((:) 'r' ((:) 'o'
                                 ((:) 'n' ((:) 'g' ([]))))))))));
                              Cons _ l2 ->
                               case l2 of {
                                Nil ->
                                 ret (unsafeCoerce monad_m) (TVar0 ((:) 'd'
                                   ((:) 'e' ((:) 'l' ((:) 'w' ((:) 'r' ((:)
                                   'o' ((:) 'n' ((:) 'g' ([]))))))))));
                                Cons _ l3 ->
                                 case l3 of {
                                  Nil ->
                                   ret (unsafeCoerce monad_m) (TVar0 ((:) 'd'
                                     ((:) 'e' ((:) 'l' ((:) 'w' ((:) 'r' ((:)
                                     'o' ((:) 'n' ((:) 'g' ([]))))))))));
                                  Cons p2 l4 ->
                                   case p2 of {
                                    Pair b1 s1 ->
                                     case b1 of {
                                      GHC.Base.True ->
                                       ret (unsafeCoerce monad_m) (TVar0 ((:)
                                         'd' ((:) 'e' ((:) 'l' ((:) 'w' ((:)
                                         'r' ((:) 'o' ((:) 'n' ((:) 'g'
                                         ([]))))))))));
                                      GHC.Base.False ->
                                       case s1 of {
                                        Inl _ ->
                                         ret (unsafeCoerce monad_m) (TVar0
                                           ((:) 'd' ((:) 'e' ((:) 'l' ((:)
                                           'w' ((:) 'r' ((:) 'o' ((:) 'n'
                                           ((:) 'g' ([]))))))))));
                                        Inr _ ->
                                         case l4 of {
                                          Nil ->
                                           ret (unsafeCoerce monad_m) (TVar0
                                             ((:) 'd' ((:) 'e' ((:) 'l' ((:)
                                             'w' ((:) 'r' ((:) 'o' ((:) 'n'
                                             ((:) 'g' ([]))))))))));
                                          Cons p3 l5 ->
                                           case p3 of {
                                            Pair b2 s2 ->
                                             case b2 of {
                                              GHC.Base.True ->
                                               ret (unsafeCoerce monad_m)
                                                 (TVar0 ((:) 'd' ((:) 'e'
                                                 ((:) 'l' ((:) 'w' ((:) 'r'
                                                 ((:) 'o' ((:) 'n' ((:) 'g'
                                                 ([]))))))))));
                                              GHC.Base.False ->
                                               case s2 of {
                                                Inl _ ->
                                                 ret (unsafeCoerce monad_m)
                                                   (TVar0 ((:) 'd' ((:) 'e'
                                                   ((:) 'l' ((:) 'w' ((:) 'r'
                                                   ((:) 'o' ((:) 'n' ((:) 'g'
                                                   ([]))))))))));
                                                Inr eq ->
                                                 case l5 of {
                                                  Nil ->
                                                   ret (unsafeCoerce monad_m)
                                                     (TDelta
                                                     (eq_elim_term eq eqty
                                                       x0));
                                                  Cons _ _ ->
                                                   ret (unsafeCoerce monad_m)
                                                     (TVar0 ((:) 'd' ((:) 'e'
                                                     ((:) 'l' ((:) 'w' ((:)
                                                     'r' ((:) 'o' ((:) 'n'
                                                     ((:) 'g' ([]))))))))))}}}}}}}}}}}}}}};
                    Inr _ ->
                     ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:) 'e' ((:)
                       'l' ((:) 'w' ((:) 'r' ((:) 'o' ((:) 'n' ((:) 'g'
                       ([]))))))))))}}}};
            _ ->
             ret (unsafeCoerce monad_m) (TVar0 ((:) 'd' ((:) 'e' ((:) 'l'
               ((:) 'w' ((:) 'r' ((:) 'o' ((:) 'n' ((:) 'g' ([]))))))))))});
        GHC.Base.False ->
         bind (unsafeCoerce monad_m)
           (unsafeCoerce localDenote monad_m reader_m x (denoteTerm0 bdy))
           (\x0 ->
           case x0 of {
            Pair bdy' x' ->
             case isKind kty of {
              GHC.Base.True ->
               bind (unsafeCoerce monad_m) (unsafeCoerce denoteKind0 kty)
                 (\k ->
                 bind (unsafeCoerce monad_m) (unsafeCoerce denoteType0 t')
                   (\t'' ->
                   ret (unsafeCoerce monad_m) (TLetTy x' k t'' bdy')));
              GHC.Base.False ->
               bind (unsafeCoerce monad_m) (unsafeCoerce denoteType0 kty)
                 (\ty ->
                 bind (unsafeCoerce monad_m) (denoteTerm0 t') (\t'' ->
                   ret (unsafeCoerce monad_m) (TLetTm x' GHC.Base.False ty
                     t'' bdy')))}})};
      TApp t0 ts ->
       bind (unsafeCoerce monad_m) (denoteTerm0 t0) (\t' ->
         bind (unsafeCoerce monad_m)
           (list_m (unsafeCoerce monad_m)
             (map (\e ->
               bind (unsafeCoerce monad_m)
                 (unsafeCoerce isType monad_m reader_m either_m e) (\b ->
                 case b of {
                  GHC.Base.True ->
                   fmap (functor_Monad (unsafeCoerce monad_m)) (\x -> Inl x)
                     (unsafeCoerce denoteType0 e);
                  GHC.Base.False ->
                   fmap (functor_Monad (unsafeCoerce monad_m)) (\x -> Inr x)
                     (denoteTerm0 e)})) ts)) (\ts' ->
           bind (unsafeCoerce monad_m)
             (unsafeCoerce reorg_app_args monad_m reader_m t' ts') (\ts'' ->
             ret (unsafeCoerce monad_m) (TApp0 t' ts''))));
      TConst kern _ ->
       ret (unsafeCoerce monad_m) (TVar0 (kername_to_qualid kern));
      TInd ind _ ->
       ret (unsafeCoerce monad_m) (TVar0
         (kername_to_qualid (inductive_mind ind)));
      TConstruct ind n _ ->
       bind (unsafeCoerce monad_m)
         (unsafeCoerce get_ctors monad_m reader_m either_m ind) (\ctors ->
         bind (unsafeCoerce monad_m)
           (option_m monad_m either_m (nth_error ctors n) ((:) 'C' ((:) 'o'
             ((:) 'u' ((:) 'l' ((:) 'd' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't'
             ((:) ' ' ((:) 'f' ((:) 'i' ((:) 'n' ((:) 'd' ((:) ' ' ((:) 'c'
             ((:) 'o' ((:) 'n' ((:) 's' ((:) 't' ((:) 'r' ((:) 'u' ((:) 'c'
             ((:) 't' ((:) 'o' ((:) 'r' ([]))))))))))))))))))))))))))))
           (\x ->
           case x of {
            Pair p0 _ ->
             case p0 of {
              Pair ctor _ -> ret (unsafeCoerce monad_m) (TVar0 ctor)}}));
      TCase ind_and_nbparams mot matchvar brchs ->
       case ind_and_nbparams of {
        Pair ind _ ->
         bind (unsafeCoerce monad_m) (ask (unsafeCoerce reader_m)) (\x ->
           case x of {
            Pair _ renv ->
             case renv of {
              Pair y _ ->
               case y of {
                Pair y0 amots ->
                 case y0 of {
                  Pair y1 anargs ->
                   case y1 of {
                    Pair arargs _ ->
                     bind (unsafeCoerce monad_m)
                       (unsafeCoerce get_ctors monad_m reader_m either_m ind)
                       (\ctors ->
                       bind (unsafeCoerce monad_m) (denoteTerm0 matchvar)
                         (\matchvar' ->
                         bind (unsafeCoerce monad_m)
                           (unsafeCoerce denoteType0 mot) (\mot' ->
                           bind (unsafeCoerce monad_m)
                             (list_m (unsafeCoerce monad_m)
                               (map
                                 (unsafeCoerce take_args monad_m reader_m
                                   either_m) brchs)) (\args ->
                             bind (unsafeCoerce monad_m)
                               (list_m (unsafeCoerce monad_m)
                                 (map (\pat ->
                                   case pat of {
                                    Pair _ t0 -> denoteTerm0 t0}) brchs))
                               (\brchs_t' ->
                               let {brchs_n = map fst brchs} in
                               let {
                                trimmed_brchs' = map (\pat ->
                                                   case pat of {
                                                    Pair n t0 ->
                                                     removeLambdas n t0})
                                                   (combine brchs_n brchs_t')}
                               in
                               let {
                                constrs = map build_tApp (combine ctors args)}
                               in
                               let {flat_constrs = map flattenTApp constrs}
                               in
                               let {fname = get_rfunc_name matchvar' arargs}
                               in
                               let {mot'0 = get_motive fname amots mot'} in
                               let {app_args = get_nrargs fname anargs} in
                               let {
                                nrargs_brchs = map (bind_nrargs app_args)
                                                 trimmed_brchs'}
                               in
                               let {
                                tapp_args = map (\x0 -> Pair GHC.Base.False
                                              (let {x1 = fst x0} in
                                               Inr (TVar0 x1))) app_args}
                               in
                               let {
                                t' = TApp0 (TMu fname matchvar' (Some mot'0)
                                 (combine flat_constrs nrargs_brchs))
                                 tapp_args}
                               in
                               ret (unsafeCoerce monad_m) (flattenTApp t'))))))}}}}})};
      TProj _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'P' ((:) 'r' ((:) 'o' ((:)
         'j' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i' ((:) 'm'
         ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:) 't' ((:)
         'e' ((:) 'd' ((:) ' ' ((:) 'y' ((:) 'e' ((:) 't'
         ([]))))))))))))))))))))))))));
      TFix mfix _ ->
       case mfix of {
        Nil ->
         raise (unsafeCoerce either_m) ((:) 'M' ((:) 'u' ((:) 't' ((:) 'u'
           ((:) 'a' ((:) 'l' ((:) 'l' ((:) 'y' ((:) ' ' ((:) 'r' ((:) 'e'
           ((:) 'c' ((:) 'u' ((:) 'r' ((:) 's' ((:) 'i' ((:) 'v' ((:) 'e'
           ((:) ' ' ((:) 'f' ((:) 'i' ((:) 'x' ((:) 'p' ((:) 'o' ((:) 'i'
           ((:) 'n' ((:) 't' ((:) 's' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't'
           ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm'
           ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y'
           ((:) 'e' ((:) 't'
           ([])))))))))))))))))))))))))))))))))))))))))))))))));
        Cons f l ->
         case l of {
          Nil ->
           let {fname = get_ident (dname f)} in
           let {body = dbody f} in
           let {type0 = dtype f} in
           let {rarg_pos = rarg f} in
           bind (unsafeCoerce monad_m) (unsafeCoerce denoteType0 type0)
             (\ty ->
             bind (unsafeCoerce monad_m)
               (unsafeCoerce denoteMotive monad_m reader_m state_m either_m
                 ty rarg_pos fname) (\renv' ->
               local (unsafeCoerce reader_m) (\pat ->
                 case pat of {
                  Pair y _ ->
                   case y of {
                    Pair genv _UU0393_ -> Pair (Pair genv (Cons fname
                     _UU0393_)) renv'}}) (denoteTerm0 body)));
          Cons _ _ ->
           raise (unsafeCoerce either_m) ((:) 'M' ((:) 'u' ((:) 't' ((:) 'u'
             ((:) 'a' ((:) 'l' ((:) 'l' ((:) 'y' ((:) ' ' ((:) 'r' ((:) 'e'
             ((:) 'c' ((:) 'u' ((:) 'r' ((:) 's' ((:) 'i' ((:) 'v' ((:) 'e'
             ((:) ' ' ((:) 'f' ((:) 'i' ((:) 'x' ((:) 'p' ((:) 'o' ((:) 'i'
             ((:) 'n' ((:) 't' ((:) 's' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't'
             ((:) ' ' ((:) 'i' ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm'
             ((:) 'e' ((:) 'n' ((:) 't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y'
             ((:) 'e' ((:) 't'
             ([])))))))))))))))))))))))))))))))))))))))))))))))))}};
      TCoFix _ _ ->
       raise (unsafeCoerce either_m) ((:) 't' ((:) 'C' ((:) 'o' ((:) 'F' ((:)
         'i' ((:) 'x' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'i'
         ((:) 'm' ((:) 'p' ((:) 'l' ((:) 'e' ((:) 'm' ((:) 'e' ((:) 'n' ((:)
         't' ((:) 'e' ((:) 'd' ((:) ' ' ((:) 'y' ((:) 'e' ((:) 't'
         ([])))))))))))))))))))))))))))}}
  in denoteTerm0

denoteCtors :: (Monad (M Any)) -> (MonadReader
               (Prod (Prod Global_env Ctx) Rec_env) (M Any)) -> (MonadState
               Params_env (M Any)) -> (MonadExc Prelude.String (M Any)) ->
               Var0 -> Params -> (Prod (Prod Ident Term) GHC.Base.Int) -> M
               Ctor
denoteCtors monad_m reader_m state_m either_m data_name _ ctor =
  case ctor of {
   Pair p0 _ ->
    case p0 of {
     Pair name t ->
      bind (unsafeCoerce monad_m)
        (local (unsafeCoerce reader_m) (\pat ->
          case pat of {
           Pair y _ ->
            case y of {
             Pair genv _ -> Pair (Pair genv (Cons data_name Nil)) fresh_renv}})
          (unsafeCoerce denoteType monad_m reader_m state_m either_m t))
        (\t' -> ret (unsafeCoerce monad_m) (Ctr name t'))}}

denoteParams :: (Monad (M Any)) -> (MonadReader
                (Prod (Prod Global_env Ctx) Rec_env) (M Any)) -> (MonadState
                Params_env (M Any)) -> (MonadExc Prelude.String (M Any)) ->
                Context -> M Params
denoteParams monad_m reader_m state_m either_m params =
  case params of {
   Nil -> ret (unsafeCoerce monad_m) Nil;
   Cons p0 ps ->
    let {x = decl_name p0} in
    let {t = decl_type p0} in
    bind (unsafeCoerce monad_m)
      (case isKind t of {
        GHC.Base.True ->
         inj1M (unsafeCoerce monad_m)
           (unsafeCoerce denoteKind monad_m reader_m state_m either_m t);
        GHC.Base.False ->
         inj2M (unsafeCoerce monad_m)
           (unsafeCoerce denoteType monad_m reader_m state_m either_m t)})
      (\tk ->
      bind (unsafeCoerce monad_m)
        (unsafeCoerce localDenote monad_m reader_m x
          (denoteParams monad_m reader_m state_m either_m ps)) (\x0 ->
        case x0 of {
         Pair ls x' ->
          ret (unsafeCoerce monad_m) (Cons (Pair (getName x') tk) ls)}))}

denoteInductive :: (Monad (M Any)) -> (MonadReader
                   (Prod (Prod Global_env Ctx) Rec_env) (M Any)) ->
                   (MonadState Params_env (M Any)) -> (MonadExc
                   Prelude.String (M Any)) -> Mutual_inductive_body -> M 
                   Cmd
denoteInductive monad_m reader_m state_m either_m mbody =
  bind (unsafeCoerce monad_m)
    (option_m monad_m either_m (hd_error (unsafeCoerce ind_bodies mbody))
      ((:) 'C' ((:) 'o' ((:) 'u' ((:) 'l' ((:) 'd' ((:) ' ' ((:) 'n' ((:) 'o'
      ((:) 't' ((:) ' ' ((:) 'f' ((:) 'i' ((:) 'n' ((:) 'd' ((:) ' ' ((:) 'b'
      ((:) 'o' ((:) 'd' ((:) 'y' ((:) ' ' ((:) 'o' ((:) 'f' ((:) ' ' ((:) 'd'
      ((:) 'e' ((:) 'f' ((:) 'i' ((:) 'n' ((:) 'i' ((:) 't' ((:) 'i' ((:) 'o'
      ((:) 'n' ([]))))))))))))))))))))))))))))))))))) (\body ->
    let {name = ind_name body} in
    case (Prelude.==) name ((:) 'F' ((:) 'a' ((:) 'l' ((:) 's' ((:) 'e'
           ([])))))) of {
     GHC.Base.True -> ret (unsafeCoerce monad_m) (CmdAssgn false_term);
     GHC.Base.False ->
      let {ctors = ind_ctors body} in
      let {param_l = rev0 (ind_params mbody)} in
      bind (unsafeCoerce monad_m)
        (unsafeCoerce denoteParams monad_m reader_m state_m either_m param_l)
        (\params ->
        let {tki = ind_type body} in
        bind (unsafeCoerce monad_m)
          (local (unsafeCoerce reader_m) (\pat ->
            case pat of {
             Pair y _ ->
              case y of {
               Pair genv _ -> Pair (Pair genv Nil) fresh_renv}})
            (unsafeCoerce denoteKind monad_m reader_m state_m either_m tki))
          (\ki ->
          bind (unsafeCoerce monad_m) (get (unsafeCoerce state_m)) (\penv ->
            bind (unsafeCoerce monad_m)
              (put (unsafeCoerce state_m)
                (alist_add string_RelDec name (length params) penv)) (\_ ->
              bind (unsafeCoerce monad_m)
                (list_m (unsafeCoerce monad_m)
                  (map
                    (unsafeCoerce denoteCtors monad_m reader_m state_m
                      either_m name (rev0 params)) ctors)) (\ctors' ->
                ret (unsafeCoerce monad_m) (CmdData (DefData name params ki
                  ctors')))))))})

denoteGenv :: (Monad (M Any)) -> (MonadReader
              (Prod (Prod Global_env Ctx) Rec_env) (M Any)) -> (MonadState
              Params_env (M Any)) -> (MonadExc Prelude.String (M Any)) ->
              Global_env -> M Program0
denoteGenv monad_m reader_m state_m either_m genv =
  case genv of {
   Nil -> ret (unsafeCoerce monad_m) Nil;
   Cons e es' ->
    case e of {
     ConstantDecl kern cbody ->
      bind (unsafeCoerce monad_m)
        (denoteGenv monad_m reader_m state_m either_m es') (\ps ->
        case (Prelude.==) kern ((:) 'C' ((:) 'o' ((:) 'q' ((:) '.' ((:) 'I'
               ((:) 'n' ((:) 'i' ((:) 't' ((:) '.' ((:) 'L' ((:) 'o' ((:) 'g'
               ((:) 'i' ((:) 'c' ((:) '.' ((:) 'F' ((:) 'a' ((:) 'l' ((:) 's'
               ((:) 'e' ((:) '_' ((:) 'i' ((:) 'n' ((:) 'd'
               ([]))))))))))))))))))))))))) of {
         GHC.Base.True ->
          ret (unsafeCoerce monad_m) (Cons (CmdAssgn false_ind_term) ps);
         GHC.Base.False ->
          case (Prelude.==) kern ((:) 'C' ((:) 'o' ((:) 'q' ((:) '.' ((:) 'L'
                 ((:) 'o' ((:) 'g' ((:) 'i' ((:) 'c' ((:) '.' ((:) 'J' ((:)
                 'M' ((:) 'e' ((:) 'q' ((:) '.' ((:) 'J' ((:) 'M' ((:) 'e'
                 ((:) 'q' ((:) '_' ((:) 'r' ((:) 'e' ((:) 'c' ((:) 't'
                 ([]))))))))))))))))))))))))) of {
           GHC.Base.True ->
            ret (unsafeCoerce monad_m) (Cons (CmdAssgn jMeq_rect_term) ps);
           GHC.Base.False ->
            case (Prelude.==) kern ((:) 'C' ((:) 'o' ((:) 'q' ((:) '.' ((:)
                   'L' ((:) 'o' ((:) 'g' ((:) 'i' ((:) 'c' ((:) '.' ((:) 'J'
                   ((:) 'M' ((:) 'e' ((:) 'q' ((:) '.' ((:) 'J' ((:) 'M' ((:)
                   'e' ((:) 'q' ((:) '_' ((:) 'e' ((:) 'q'
                   ([]))))))))))))))))))))))) of {
             GHC.Base.True -> ret (unsafeCoerce monad_m) ps;
             GHC.Base.False ->
              bind (unsafeCoerce monad_m)
                (option_m monad_m either_m (unsafeCoerce cst_body cbody)
                  (append ((:) 'C' ((:) 'o' ((:) 'n' ((:) 's' ((:) 't' ((:)
                    'a' ((:) 'n' ((:) 't' ((:) ' ' ([]))))))))))
                    (append kern ((:) ' ' ((:) 'd' ((:) 'o' ((:) 'e' ((:) 's'
                      ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'h'
                      ((:) 'a' ((:) 'v' ((:) 'e' ((:) ' ' ((:) 'a' ((:) ' '
                      ((:) 'b' ((:) 'o' ((:) 'd' ((:) 'y' ((:) ' ' ((:) 'd'
                      ((:) 'e' ((:) 'f' ((:) 'i' ((:) 'n' ((:) 'e' ((:) 'd'
                      ([]))))))))))))))))))))))))))))))))) (\bdy ->
                let {name = kername_to_qualid kern} in
                case isKind (cst_type cbody) of {
                 GHC.Base.True ->
                  bind (unsafeCoerce monad_m)
                    (unsafeCoerce denoteType monad_m reader_m state_m
                      either_m bdy) (\ty ->
                    bind (unsafeCoerce monad_m)
                      (unsafeCoerce denoteKind monad_m reader_m state_m
                        either_m (cst_type cbody)) (\k ->
                      let {asgn = CmdAssgn (AssgnType name (Some k) ty)} in
                      ret (unsafeCoerce monad_m) (Cons asgn ps)));
                 GHC.Base.False ->
                  bind (unsafeCoerce monad_m)
                    (unsafeCoerce denoteTerm monad_m reader_m state_m
                      either_m bdy) (\t ->
                    bind (unsafeCoerce monad_m)
                      (unsafeCoerce denoteType monad_m reader_m state_m
                        either_m (cst_type cbody)) (\ty ->
                      let {asgn = CmdAssgn (AssgnTerm name (Some ty) t)} in
                      ret (unsafeCoerce monad_m) (Cons asgn ps)))})}}});
     InductiveDecl _ mbody ->
      bind (unsafeCoerce monad_m)
        (unsafeCoerce denoteInductive monad_m reader_m state_m either_m
          mbody) (\p0 ->
        bind (unsafeCoerce monad_m)
          (denoteGenv monad_m reader_m state_m either_m es') (\ps ->
          ret (unsafeCoerce monad_m) (Cons p0 ps)))}}

denoteCoq' :: (Monad (M Any)) -> (MonadReader
              (Prod (Prod Global_env Ctx) Rec_env) (M Any)) -> (MonadState
              Params_env (M Any)) -> (MonadExc Prelude.String (M Any)) ->
              Term -> M Program0
denoteCoq' monad_m reader_m state_m either_m _ =
  bind (unsafeCoerce monad_m) (ask (unsafeCoerce reader_m)) (\x ->
    case x of {
     Pair y _ ->
      case y of {
       Pair genv _ -> denoteGenv monad_m reader_m state_m either_m genv}})

m_Monad :: Monad (M Any)
m_Monad =
  monad_stateT (monad_readerT (monad_eitherT monad_ident))

m_MonadReader :: MonadReader (Prod (Prod Global_env Ctx) Rec_env) (M Any)
m_MonadReader =
  monadReader_stateT (monad_readerT (monad_eitherT monad_ident))
    (monadReader_readerT (monad_eitherT monad_ident))

m_MonadExc :: MonadExc Prelude.String (M Any)
m_MonadExc =
  exc_stateT (monad_readerT (monad_eitherT monad_ident))
    (monadExc_readerT (exception_eitherT monad_ident))

m_MonadState :: MonadState Params_env (M Any)
m_MonadState =
  monadState_stateT (monad_readerT (monad_eitherT monad_ident))

denoteCoq :: Program -> Sum Prelude.String Program0
denoteCoq p0 =
  case p0 of {
   Pair genv t ->
    case run_m Nil (Pair (Pair genv Nil) fresh_renv)
           (denoteCoq' m_Monad m_MonadReader m_MonadState m_MonadExc t) of {
     Inl l -> Inl l;
     Inr p1 -> case p1 of {
                Pair p2 _ -> Inr p2}}}

tkStar :: Prelude.String
tkStar = ['★']

tkArrow :: Prelude.String
tkArrow = ['➔']

tkSpace :: Prelude.String
tkSpace =
  (:) ' ' ([])

tkColon :: Prelude.String
tkColon =
  (:) ':' ([])

tkPipe :: Prelude.String
tkPipe =
  (:) '|' ([])

tkDot :: Prelude.String
tkDot =
  (:) '.' ([])

tkTab :: Prelude.String
tkTab =
  (:) ' ' ((:) ' ' ([]))

tkPi :: Prelude.String
tkPi = ['Π']

tkAll :: Prelude.String
tkAll = ['∀']

tkOpenPar :: Prelude.String
tkOpenPar =
  (:) '(' ([])

tkOpenBrac :: Prelude.String
tkOpenBrac =
  (:) '[' ([])

tkOpenCBrac :: Prelude.String
tkOpenCBrac =
  (:) '{' ([])

tkCloseCBrac :: Prelude.String
tkCloseCBrac =
  (:) '}' ([])

tkCloseBrac :: Prelude.String
tkCloseBrac =
  (:) ']' ([])

tkClosePar :: Prelude.String
tkClosePar =
  (:) ')' ([])

tkDash :: Prelude.String
tkDash =
  (:) '-' ([])

tkTDot :: Prelude.String
tkTDot = ['·']

tkData :: Prelude.String
tkData =
  (:) 'd' ((:) 'a' ((:) 't' ((:) 'a' ([]))))

tkLam :: Prelude.String
tkLam = ['λ']

tkULam :: Prelude.String
tkULam = ['Λ']

tkMu :: Prelude.String
tkMu = ['μ']

tkSigma :: Prelude.String
tkSigma = ['σ']

tkDelta :: Prelude.String
tkDelta = ['δ']

tkBeta :: Prelude.String
tkBeta = ['β']

tkRho :: Prelude.String
tkRho =
  (:) '\207' ((:) '\129' ([]))

tkEq :: Prelude.String
tkEq = ['≃']

tkAt :: Prelude.String
tkAt =
  (:) '@' ([])

tkAssgn :: Prelude.String
tkAssgn =
  (:) '=' ([])

tkErase :: Prelude.String
tkErase =
  (:) '-' ([])

tkCR :: Prelude.String
tkCR =
  (:) '\n' ([])

type Pretty p = p -> Prelude.String

pretty :: (Pretty a1) -> a1 -> Prelude.String
pretty pretty0 =
  pretty0

prettySum :: (Pretty a1) -> Pretty (Sum Prelude.String a1)
prettySum x y =
  case y of {
   Inl s -> s;
   Inr a -> pretty x a}

type Type_ctx = Alist Var0 (Sum Kind Typ)

string_RelDec0 :: RelDec Prelude.String
string_RelDec0 =
  (Prelude.==)

ppIndentation :: GHC.Base.Int -> Prelude.String
ppIndentation n =
  (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
    (\_ -> ([]))
    (\n0 -> append tkTab (ppIndentation n0))
    n

string_of_list_aux :: (a1 -> Prelude.String) -> Prelude.String -> (List 
                      a1) -> GHC.Base.Int -> Prelude.String
string_of_list_aux f sep l indentation =
  case l of {
   Nil -> ([]);
   Cons a l0 ->
    case l0 of {
     Nil -> append (ppIndentation indentation) (f a);
     Cons _ _ ->
      append (ppIndentation indentation)
        (append (f a) (append sep (string_of_list_aux f sep l0 indentation)))}}

string_of_list :: (a1 -> Prelude.String) -> (List a1) -> GHC.Base.Int ->
                  Prelude.String
string_of_list f l indentation =
  string_of_list_aux f tkCR l indentation

parens :: GHC.Base.Bool -> Prelude.String -> Prelude.String
parens b s =
  case b of {
   GHC.Base.True -> append tkOpenPar (append s tkClosePar);
   GHC.Base.False -> s}

getVarTyp :: Typ -> Option Var0
getVarTyp t =
  case t of {
   TyVar v -> Some v;
   TyAll _ _ t' -> getVarTyp t';
   TyPi _ _ t' -> getVarTyp t';
   TyApp t' _ -> getVarTyp t';
   TyLam _ _ t' -> getVarTyp t';
   TyLamK _ _ t' -> getVarTyp t';
   TyAllT _ _ t' -> getVarTyp t';
   _ -> None}

getVarTerm :: Term0 -> Option Var0
getVarTerm t =
  case t of {
   TVar0 v -> Some v;
   TLam _ _ _ t' -> getVarTerm t';
   TLamK _ _ t' -> getVarTerm t';
   TApp0 t' _ -> getVarTerm t';
   TLetTm _ _ _ _ t' -> getVarTerm t';
   TLetTy _ _ _ t' -> getVarTerm t';
   _ -> None}

getVar :: (Sum Typ Term0) -> Option Var0
getVar t =
  case t of {
   Inl t' -> getVarTyp t';
   Inr t' -> getVarTerm t'}

ppDot :: GHC.Base.Bool -> (Sum Typ Term0) -> State Type_ctx Prelude.String
ppDot b t =
  case b of {
   GHC.Base.True -> ret (unsafeCoerce monad_state) tkErase;
   GHC.Base.False ->
    bind (unsafeCoerce monad_state) (get (unsafeCoerce monadState_state))
      (\_UU0393_ ->
      case getVar t of {
       Some v ->
        case alist_find string_RelDec0 v _UU0393_ of {
         Some t0 ->
          case t0 of {
           Inl _ -> ret (unsafeCoerce monad_state) tkTDot;
           Inr _ -> ret (unsafeCoerce monad_state) ([])};
         None -> ret (unsafeCoerce monad_state) ([])};
       None -> ret (unsafeCoerce monad_state) ([])})}

appendCtx :: Var0 -> (Sum Kind Typ) -> State Type_ctx Unit
appendCtx v t =
  bind (unsafeCoerce monad_state) (get (unsafeCoerce monadState_state))
    (\_UU0393_ ->
    put (unsafeCoerce monadState_state)
      (alist_add string_RelDec0 v t _UU0393_))

getName0 :: Name0 -> Var0
getName0 x =
  case x of {
   Anon -> (:) '_' ([]);
   Named n -> n}

flattenApp :: Typ -> Typ
flattenApp t =
  case t of {
   TyApp t' l -> case l of {
                  Nil -> t';
                  Cons _ _ -> t};
   _ -> t}

ppKind :: Kind -> State Type_ctx Prelude.String
ppKind ki =
  case ki of {
   KdStar -> ret (unsafeCoerce monad_state) tkStar;
   KdAll x k1 k2 ->
    bind (unsafeCoerce monad_state)
      (case k1 of {
        Inl ki1 -> ppKind ki1;
        Inr ty1 -> ppTyp GHC.Base.False GHC.Base.False ty1}) (\k1' ->
      bind (unsafeCoerce monad_state) (ppKind k2) (\k2' ->
        case x of {
         Anon ->
          ret (unsafeCoerce monad_state)
            (append k1'
              (append tkSpace (append tkArrow (append tkSpace k2'))));
         Named name ->
          ret (unsafeCoerce monad_state)
            (append tkPi
              (append tkSpace
                (append name
                  (append tkSpace
                    (append tkColon
                      (append tkSpace
                        (append k1'
                          (append tkSpace
                            (append tkDot (append tkSpace k2'))))))))))}))}

ppTyp :: GHC.Base.Bool -> GHC.Base.Bool -> Typ -> State Type_ctx
         Prelude.String
ppTyp barr bapp t =
  case t of {
   TyVar v -> ret (unsafeCoerce monad_state) v;
   TyAll x t1 t2 ->
    let {name = getName0 x} in
    bind (unsafeCoerce monad_state) (ppKind t1) (\k ->
      bind (unsafeCoerce monad_state) (unsafeCoerce appendCtx name (Inl t1))
        (\_ ->
        bind (unsafeCoerce monad_state)
          (ppTyp GHC.Base.False GHC.Base.False t2) (\t2' ->
          ret (unsafeCoerce monad_state)
            (append tkAll
              (append tkSpace
                (append name
                  (append tkSpace
                    (append tkColon
                      (append tkSpace
                        (append k
                          (append tkSpace
                            (append tkDot (append tkSpace t2')))))))))))));
   TyPi x t1 t2 ->
    case x of {
     Anon ->
      bind (unsafeCoerce monad_state) (ppTyp GHC.Base.True GHC.Base.False t1)
        (\t1' ->
        bind (unsafeCoerce monad_state)
          (ppTyp GHC.Base.False GHC.Base.False t2) (\t2' ->
          ret (unsafeCoerce monad_state)
            (parens barr
              (append t1'
                (append tkSpace (append tkArrow (append tkSpace t2')))))));
     Named name ->
      bind (unsafeCoerce monad_state)
        (ppTyp GHC.Base.False GHC.Base.False t1) (\t1' ->
        bind (unsafeCoerce monad_state)
          (unsafeCoerce appendCtx name (Inr t1)) (\_ ->
          bind (unsafeCoerce monad_state)
            (ppTyp GHC.Base.False GHC.Base.False t2) (\t2' ->
            ret (unsafeCoerce monad_state)
              (append tkPi
                (append tkSpace
                  (append name
                    (append tkSpace
                      (append tkColon
                        (append tkSpace
                          (append t1'
                            (append tkSpace
                              (append tkDot (append tkSpace t2')))))))))))))};
   TyApp t1 ts2 ->
    bind (unsafeCoerce monad_state) (ppTyp GHC.Base.False GHC.Base.True t1)
      (\t1' ->
      let {
       ppApp = \bt ->
        case bt of {
         Pair b t0 ->
          bind monad_state (unsafeCoerce ppDot b t0) (\d ->
            case t0 of {
             Inl t' ->
              bind monad_state
                (unsafeCoerce ppTyp GHC.Base.False GHC.Base.True t') (\t'' ->
                ret monad_state (append d t''));
             Inr t' ->
              bind monad_state
                (unsafeCoerce ppTerm GHC.Base.False GHC.Base.True t')
                (\t'' -> ret monad_state (append d t''))})}}
      in
      bind (unsafeCoerce monad_state)
        (list_m (unsafeCoerce monad_state) (map (unsafeCoerce ppApp) ts2))
        (\ts2' ->
        ret (unsafeCoerce monad_state)
          (parens bapp
            (append t1'
              (append tkSpace (string_of_list_aux id tkSpace ts2' 0))))));
   TyLam x t1 t2 ->
    let {name = getName0 x} in
    bind (unsafeCoerce monad_state)
      (case t1 of {
        Some u ->
         bind (unsafeCoerce monad_state)
           (ppTyp GHC.Base.False GHC.Base.False u) (\u' ->
           bind (unsafeCoerce monad_state)
             (unsafeCoerce appendCtx name (Inr u)) (\_ ->
             ret (unsafeCoerce monad_state)
               (append tkSpace (append tkColon (append tkSpace u')))));
        None ->
         bind (unsafeCoerce monad_state)
           (unsafeCoerce appendCtx name (Inr (TyVar ((:) '_' ([]))))) (\_ ->
           ret (unsafeCoerce monad_state) ([]))}) (\t1' ->
      bind (unsafeCoerce monad_state)
        (ppTyp GHC.Base.False GHC.Base.False t2) (\t2' ->
        ret (unsafeCoerce monad_state)
          (append tkLam
            (append tkSpace
              (append name
                (append t1'
                  (append tkSpace (append tkDot (append tkSpace t2')))))))));
   TyLamK x k t2 ->
    let {name = getName0 x} in
    bind (unsafeCoerce monad_state)
      (case k of {
        Some u ->
         bind (unsafeCoerce monad_state) (ppKind u) (\u' ->
           bind (unsafeCoerce monad_state)
             (unsafeCoerce appendCtx name (Inl u)) (\_ ->
             ret (unsafeCoerce monad_state)
               (append tkSpace (append tkColon (append tkSpace u')))));
        None ->
         bind (unsafeCoerce monad_state)
           (unsafeCoerce appendCtx name (Inl KdStar)) (\_ ->
           ret (unsafeCoerce monad_state) ([]))}) (\k' ->
      bind (unsafeCoerce monad_state)
        (ppTyp GHC.Base.False GHC.Base.False t2) (\t2' ->
        ret (unsafeCoerce monad_state)
          (append tkLam
            (append tkSpace
              (append name
                (append k'
                  (append tkSpace (append tkDot (append tkSpace t2')))))))));
   TyEq t1 t2 ->
    bind (unsafeCoerce monad_state) (ppTerm GHC.Base.False GHC.Base.False t1)
      (\t1' ->
      bind (unsafeCoerce monad_state)
        (ppTerm GHC.Base.False GHC.Base.False t2) (\t2' ->
        ret (unsafeCoerce monad_state)
          (append tkOpenCBrac
            (append tkSpace
              (append t1'
                (append tkSpace
                  (append tkEq
                    (append tkSpace
                      (append t2' (append tkSpace tkCloseCBrac))))))))));
   _ -> ret (unsafeCoerce monad_state) ((:) '?' ([]))}

ppTerm :: GHC.Base.Bool -> GHC.Base.Bool -> Term0 -> State Type_ctx
          Prelude.String
ppTerm _ bapp t =
  case t of {
   TVar0 v -> ret (unsafeCoerce monad_state) v;
   TLam x b ty t0 ->
    let {name = getName0 x} in
    bind (unsafeCoerce monad_state)
      (case ty of {
        Some u ->
         bind (unsafeCoerce monad_state)
           (ppTyp GHC.Base.False GHC.Base.False u) (\u' ->
           bind (unsafeCoerce monad_state)
             (unsafeCoerce appendCtx name (Inr u)) (\_ ->
             ret (unsafeCoerce monad_state)
               (append tkSpace (append tkColon (append tkSpace u')))));
        None ->
         bind (unsafeCoerce monad_state)
           (unsafeCoerce appendCtx name (Inr (TyVar ((:) '_' ([]))))) (\_ ->
           ret (unsafeCoerce monad_state) ([]))}) (\ty' ->
      bind (unsafeCoerce monad_state)
        (ppTerm GHC.Base.False GHC.Base.False t0) (\t' ->
        let {
         tk = case b of {
               GHC.Base.True -> tkULam;
               GHC.Base.False -> tkLam}}
        in
        ret (unsafeCoerce monad_state)
          (parens bapp
            (append tk
              (append tkSpace
                (append name
                  (append ty'
                    (append tkSpace (append tkDot (append tkSpace t'))))))))));
   TLamK x k t0 ->
    let {name = getName0 x} in
    bind (unsafeCoerce monad_state)
      (case k of {
        Some u ->
         bind (unsafeCoerce monad_state) (ppKind u) (\u' ->
           bind (unsafeCoerce monad_state)
             (unsafeCoerce appendCtx name (Inl u)) (\_ ->
             ret (unsafeCoerce monad_state)
               (append tkSpace (append tkColon (append tkSpace u')))));
        None ->
         bind (unsafeCoerce monad_state)
           (unsafeCoerce appendCtx name (Inl KdStar)) (\_ ->
           ret (unsafeCoerce monad_state) ([]))}) (\k' ->
      bind (unsafeCoerce monad_state)
        (ppTerm GHC.Base.False GHC.Base.False t0) (\t' ->
        ret (unsafeCoerce monad_state)
          (parens bapp
            (append tkULam
              (append tkSpace
                (append name
                  (append k'
                    (append tkSpace (append tkDot (append tkSpace t'))))))))));
   TApp0 t1 ts2 ->
    bind (unsafeCoerce monad_state) (ppTerm GHC.Base.False GHC.Base.True t1)
      (\t1' ->
      let {
       ppApp = \bt ->
        case bt of {
         Pair b t0 ->
          bind monad_state (unsafeCoerce ppDot b t0) (\d ->
            case t0 of {
             Inl t' ->
              bind monad_state
                (unsafeCoerce ppTyp GHC.Base.False GHC.Base.True t') (\t'' ->
                ret monad_state (append d t''));
             Inr t' ->
              bind monad_state
                (unsafeCoerce ppTerm GHC.Base.False GHC.Base.True t')
                (\t'' -> ret monad_state (append d t''))})}}
      in
      bind (unsafeCoerce monad_state)
        (list_m (unsafeCoerce monad_state) (map (unsafeCoerce ppApp) ts2))
        (\ts2' ->
        ret (unsafeCoerce monad_state)
          (parens bapp
            (append t1'
              (append tkSpace (string_of_list_aux id tkSpace ts2' 0))))));
   TLetTm x _ ty t0 bdy ->
    bind (unsafeCoerce monad_state) (ppTyp GHC.Base.False GHC.Base.False ty)
      (\ty' ->
      let {name = getName0 x} in
      bind (unsafeCoerce monad_state)
        (ppTerm GHC.Base.False GHC.Base.False t0) (\t' ->
        bind (unsafeCoerce monad_state)
          (unsafeCoerce appendCtx name (Inr ty)) (\_ ->
          bind (unsafeCoerce monad_state)
            (ppTerm GHC.Base.False GHC.Base.False bdy) (\bdy' ->
            ret (unsafeCoerce monad_state)
              (append tkOpenBrac
                (append tkSpace
                  (append name
                    (append tkSpace
                      (append tkColon
                        (append tkSpace
                          (append ty'
                            (append tkSpace
                              (append tkAssgn
                                (append tkSpace
                                  (append t'
                                    (append tkSpace
                                      (append tkCloseBrac
                                        (append tkSpace
                                          (append tkDash
                                            (append tkSpace bdy'))))))))))))))))))));
   TLetTy x k ty bdy ->
    bind (unsafeCoerce monad_state) (ppKind k) (\k' ->
      let {name = getName0 x} in
      bind (unsafeCoerce monad_state)
        (ppTyp GHC.Base.False GHC.Base.False ty) (\ty' ->
        bind (unsafeCoerce monad_state) (unsafeCoerce appendCtx name (Inl k))
          (\_ ->
          bind (unsafeCoerce monad_state)
            (ppTerm GHC.Base.False GHC.Base.False bdy) (\bdy' ->
            ret (unsafeCoerce monad_state)
              (append tkOpenBrac
                (append tkSpace
                  (append name
                    (append tkSpace
                      (append tkColon
                        (append tkSpace
                          (append k'
                            (append tkSpace
                              (append tkAssgn
                                (append tkSpace
                                  (append ty'
                                    (append tkSpace
                                      (append tkCloseBrac
                                        (append tkSpace
                                          (append tkDash
                                            (append tkSpace bdy'))))))))))))))))))));
   TMu b t0 mot brchs ->
    let {
     printBranch = \brch ->
      case brch of {
       Pair t1 t2 ->
        bind monad_state
          (unsafeCoerce ppTerm GHC.Base.False GHC.Base.False t1) (\t1' ->
          bind monad_state
            (unsafeCoerce ppTerm GHC.Base.False GHC.Base.False t2) (\t2' ->
            ret monad_state
              (append tkPipe
                (append tkSpace
                  (append t1'
                    (append tkSpace
                      (append tkArrow (append tkSpace (append t2' tkSpace)))))))))}}
    in
    let {
     printMotive = \mmot ->
      case mmot of {
       Some mot0 ->
        bind monad_state
          (unsafeCoerce ppTyp GHC.Base.False GHC.Base.False mot0) (\mot' ->
          ret monad_state
            (append tkAt
              (append tkOpenPar (append mot' (append tkClosePar tkSpace)))));
       None -> ret monad_state ([])}}
    in
    bind (unsafeCoerce monad_state) (ppTerm GHC.Base.False GHC.Base.False t0)
      (\t' ->
      bind (unsafeCoerce monad_state) (unsafeCoerce printMotive mot)
        (\mot' ->
        let {
         rec = case b of {
                Some s -> append tkMu (append tkSpace (append s tkDot));
                None -> tkSigma}}
        in
        bind (unsafeCoerce monad_state)
          (list_m (unsafeCoerce monad_state)
            (map (unsafeCoerce printBranch) brchs)) (\brchs' ->
          ret (unsafeCoerce monad_state)
            (append rec
              (append tkSpace
                (append t'
                  (append tkSpace
                    (append mot'
                      (append tkOpenCBrac
                        (append tkCR
                          (append
                            (string_of_list id brchs' ((\ x -> x Prelude.+ 1)
                              0))
                            (append tkCR (append tkSpace tkCloseCBrac)))))))))))));
   TDelta t0 ->
    bind (unsafeCoerce monad_state) (ppTerm GHC.Base.False GHC.Base.False t0)
      (\t' ->
      ret (unsafeCoerce monad_state)
        (append tkDelta
          (append tkSpace
            (append tkDash
              (append tkSpace
                (append tkOpenPar (append tkSpace (append t' tkClosePar))))))));
   TRho t1 t2 ->
    bind (unsafeCoerce monad_state) (ppTerm GHC.Base.False GHC.Base.False t1)
      (\lhs ->
      bind (unsafeCoerce monad_state)
        (ppTerm GHC.Base.False GHC.Base.False t2) (\rhs ->
        ret (unsafeCoerce monad_state)
          (append tkRho
            (append tkSpace
              (append lhs
                (append tkSpace (append tkDash (append tkSpace rhs))))))));
   TBeta -> ret (unsafeCoerce monad_state) tkBeta}

runPpKind :: Kind -> Type_ctx -> Prelude.String
runPpKind ki _UU0393_ =
  fst (runState (ppKind ki) _UU0393_)

runPpTyp :: Typ -> Type_ctx -> Prelude.String
runPpTyp t _UU0393_ =
  fst (runState (ppTyp GHC.Base.False GHC.Base.False t) _UU0393_)

appendNamed :: Name0 -> (Sum Kind Typ) -> State Type_ctx Unit
appendNamed x kty =
  case x of {
   Anon -> ret (unsafeCoerce monad_state) Tt;
   Named name -> appendCtx name kty}

removeBindingsTyp :: Typ -> GHC.Base.Int -> State Type_ctx Typ
removeBindingsTyp t n =
  (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
    (\_ -> ret (unsafeCoerce monad_state) t)
    (\_ ->
    case t of {
     TyAll x k t2 ->
      bind (unsafeCoerce monad_state) (removeBindingsTyp t2 (pred n)) (\t' ->
        bind (unsafeCoerce monad_state) (unsafeCoerce appendNamed x (Inl k))
          (\_ -> ret (unsafeCoerce monad_state) t'));
     TyPi x t1 t2 ->
      bind (unsafeCoerce monad_state) (removeBindingsTyp t2 (pred n)) (\t' ->
        bind (unsafeCoerce monad_state) (unsafeCoerce appendNamed x (Inr t1))
          (\_ -> ret (unsafeCoerce monad_state) t'));
     _ -> ret (unsafeCoerce monad_state) t})
    n

removeBindingsK :: Kind -> GHC.Base.Int -> State Type_ctx Kind
removeBindingsK k n =
  (\ zero succ n -> if n GHC.Base.== 0 then zero () else succ (n Prelude.- 1))
    (\_ -> ret (unsafeCoerce monad_state) k)
    (\_ ->
    case k of {
     KdStar -> ret (unsafeCoerce monad_state) k;
     KdAll x _ k2 ->
      bind (unsafeCoerce monad_state) (removeBindingsK k2 (pred n)) (\k' ->
        bind (unsafeCoerce monad_state) (unsafeCoerce appendNamed x (Inl k))
          (\_ -> ret (unsafeCoerce monad_state) k'))})
    n

removeParams :: Var0 -> GHC.Base.Int -> Typ -> Typ
removeParams data_name params_count t =
  let {removeParams' = removeParams data_name params_count} in
  case t of {
   TyPi x t1 t2 -> TyPi x (removeParams' t1) (removeParams' t2);
   TyApp t1 ts2 ->
    case t1 of {
     TyVar v ->
      case (Prelude.==) v data_name of {
       GHC.Base.True ->
        let {rs' = skipn params_count ts2} in flattenApp (TyApp t1 rs');
       GHC.Base.False -> flattenApp (TyApp t1 ts2)};
     _ -> TyApp (removeParams' t1) ts2};
   _ -> t}

ppctor :: GHC.Base.Int -> Var0 -> Ctor -> State Type_ctx Prelude.String
ppctor params_count data_name ctor =
  case ctor of {
   Ctr cname ty ->
    bind (unsafeCoerce monad_state)
      (unsafeCoerce removeBindingsTyp ty params_count) (\no_bindings_t ->
      let {no_params_t = removeParams data_name params_count no_bindings_t}
      in
      bind (unsafeCoerce monad_state) (get (unsafeCoerce monadState_state))
        (\_UU0393_ ->
        bind (unsafeCoerce monad_state)
          (ppTyp GHC.Base.False GHC.Base.False no_params_t) (\t' ->
          bind (unsafeCoerce monad_state)
            (put (unsafeCoerce monadState_state) _UU0393_) (\_ ->
            ret (unsafeCoerce monad_state)
              (append tkPipe
                (append tkSpace
                  (append cname
                    (append tkSpace (append tkColon (append tkSpace t'))))))))))}

prettyParams :: Pretty Params
prettyParams params =
  case params of {
   Nil -> ([]);
   Cons p0 ps ->
    case p0 of {
     Pair n t ->
      let {
       t' = case t of {
             Inl k -> runPpKind k Nil;
             Inr ty -> runPpTyp ty Nil}}
      in
      append tkSpace
        (append tkOpenPar
          (append n
            (append tkSpace
              (append tkColon
                (append tkSpace
                  (append t' (append tkClosePar (prettyParams ps))))))))}}

ppDatatype :: Var0 -> Params -> Kind -> (List Ctor) -> State Type_ctx
              Prelude.String
ppDatatype name params ki ctors =
  bind (unsafeCoerce monad_state)
    (unsafeCoerce removeBindingsK ki (length params)) (\noparams_kind ->
    bind (unsafeCoerce monad_state) (ppKind noparams_kind) (\ki' ->
      bind (unsafeCoerce monad_state)
        (list_m (unsafeCoerce monad_state)
          (map (ppctor (length params) name) ctors)) (\ctorlist ->
        let {ctors' = string_of_list id ctorlist ((\ x -> x Prelude.+ 1) 0)}
        in
        ret (unsafeCoerce monad_state)
          (append tkData
            (append tkSpace
              (append name
                (append (pretty prettyParams params)
                  (append tkSpace
                    (append tkColon
                      (append tkSpace
                        (append ki'
                          (append tkSpace
                            (append tkAssgn
                              (append tkCR (append ctors' tkDot)))))))))))))))

ppmKind :: Var0 -> (Option Kind) -> State Type_ctx Prelude.String
ppmKind v mki =
  case mki of {
   Some ki ->
    bind (unsafeCoerce monad_state) (ppKind ki) (\ki' ->
      bind (unsafeCoerce monad_state) (unsafeCoerce appendCtx v (Inl ki))
        (\_ ->
        ret (unsafeCoerce monad_state)
          (append tkColon (append tkSpace (append ki' tkSpace)))));
   None -> ret (unsafeCoerce monad_state) ([])}

ppmType :: Var0 -> (Option Typ) -> State Type_ctx Prelude.String
ppmType v mty =
  case mty of {
   Some ty ->
    bind (unsafeCoerce monad_state) (ppTyp GHC.Base.False GHC.Base.False ty)
      (\ty' ->
      bind (unsafeCoerce monad_state) (unsafeCoerce appendCtx v (Inr ty))
        (\_ ->
        ret (unsafeCoerce monad_state)
          (append tkColon (append tkSpace (append ty' tkSpace)))));
   None -> ret (unsafeCoerce monad_state) ([])}

ppCmd :: Cmd -> State Type_ctx Prelude.String
ppCmd c =
  bind (unsafeCoerce monad_state) (get (unsafeCoerce monadState_state))
    (\_ ->
    case c of {
     CmdAssgn a ->
      case a of {
       AssgnTerm v mty t ->
        let {v0 = unsafeCoerce v} in
        let {mty0 = unsafeCoerce mty} in
        let {t0 = unsafeCoerce t} in
        unsafeCoerce bind monad_state (unsafeCoerce ppmType v0 mty0) (\typ ->
          bind monad_state
            (unsafeCoerce ppTerm GHC.Base.False GHC.Base.False t0) (\t' ->
            ret monad_state
              (append v0
                (append tkSpace
                  (append typ
                    (append tkAssgn
                      (append tkSpace (append t' (append tkDot tkCR)))))))));
       AssgnType v mki t ->
        let {v0 = unsafeCoerce v} in
        let {mki0 = unsafeCoerce mki} in
        let {t0 = unsafeCoerce t} in
        unsafeCoerce bind monad_state (unsafeCoerce ppmKind v0 mki0) (\ki ->
          bind monad_state
            (unsafeCoerce ppTyp GHC.Base.False GHC.Base.False t0) (\t' ->
            ret monad_state
              (append v0
                (append tkSpace
                  (append ki
                    (append tkAssgn
                      (append tkSpace (append t' (append tkDot tkCR)))))))))};
     CmdData d ->
      case d of {
       DefData name params kty ctors ->
        let {name0 = unsafeCoerce name} in
        let {params0 = unsafeCoerce params} in
        let {kty0 = unsafeCoerce kty} in
        let {ctors0 = unsafeCoerce ctors} in
        unsafeCoerce bind monad_state
          (unsafeCoerce appendCtx name0 (Inl kty0)) (\_ ->
          bind monad_state
            (unsafeCoerce ppDatatype name0 params0 kty0 ctors0) (\s ->
            ret monad_state (append s tkCR)))}})

ppProgram' :: Program0 -> State Type_ctx Prelude.String
ppProgram' p0 =
  case p0 of {
   Nil -> ret (unsafeCoerce monad_state) ([]);
   Cons c cs ->
    bind (unsafeCoerce monad_state) (ppCmd c) (\c' ->
      bind (unsafeCoerce monad_state) (ppProgram' cs) (\cs' ->
        ret (unsafeCoerce monad_state) (append c' (append tkCR cs'))))}

prettyProgram :: Pretty Program0
prettyProgram p0 =
  fst (runState (ppProgram' p0) Nil)

p :: Program
p =
  Pair (Cons (ConstantDecl ((:) 'C' ((:) 'o' ((:) 'q' ((:) '.' ((:) 'I' ((:)
    'n' ((:) 'i' ((:) 't' ((:) '.' ((:) 'D' ((:) 'a' ((:) 't' ((:) 'a' ((:)
    't' ((:) 'y' ((:) 'p' ((:) 'e' ((:) 's' ((:) '.' ((:) 'I' ((:) 'D' ((:)
    'P' ((:) 'r' ((:) 'o' ((:) 'p' ([]))))))))))))))))))))))))))
    (Build_constant_body (TSort (make'' (Pair LProp GHC.Base.False) Nil))
    (Some (TProd (NNamed ((:) 'A' ([]))) (TSort
    (make'' (Pair LProp GHC.Base.False) Nil)) (TProd NAnon (TRel 0) (TRel
    ((\ x -> x Prelude.+ 1) 0))))) (Monomorphic_ctx (Pair (of_list Nil)
    empty2)))) (Cons (ConstantDecl ((:) 'C' ((:) 'o' ((:) 'q' ((:) '.' ((:)
    'I' ((:) 'n' ((:) 'i' ((:) 't' ((:) '.' ((:) 'D' ((:) 'a' ((:) 't' ((:)
    'a' ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:) 's' ((:) '.' ((:) 'i' ((:)
    'd' ((:) 'P' ((:) 'r' ((:) 'o' ((:) 'p' ([]))))))))))))))))))))))))))
    (Build_constant_body (TConst ((:) 'C' ((:) 'o' ((:) 'q' ((:) '.' ((:) 'I'
    ((:) 'n' ((:) 'i' ((:) 't' ((:) '.' ((:) 'D' ((:) 'a' ((:) 't' ((:) 'a'
    ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:) 's' ((:) '.' ((:) 'I' ((:) 'D'
    ((:) 'P' ((:) 'r' ((:) 'o' ((:) 'p' ([])))))))))))))))))))))))))) Nil)
    (Some (TLambda (NNamed ((:) 'A' ([]))) (TSort
    (make'' (Pair LProp GHC.Base.False) Nil)) (TLambda (NNamed ((:) 'x'
    ([]))) (TRel 0) (TRel 0)))) (Monomorphic_ctx (Pair (of_list Nil)
    empty2)))) Nil)) (TConst ((:) 'C' ((:) 'o' ((:) 'q' ((:) '.' ((:) 'I'
    ((:) 'n' ((:) 'i' ((:) 't' ((:) '.' ((:) 'D' ((:) 'a' ((:) 't' ((:) 'a'
    ((:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:) 's' ((:) '.' ((:) 'i' ((:) 'd'
    ((:) 'P' ((:) 'r' ((:) 'o' ((:) 'p' ([])))))))))))))))))))))))))) Nil)

