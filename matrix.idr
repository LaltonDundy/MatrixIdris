module Matrix

import Data.Vect as V

%default total 

-- Weak Num class since (Vect n t) cant define `fromInteger` in Num
interface Num' a where
  add' : a -> a -> a
  mult': a -> a -> a

(Num a) => Num' a where
  add'  = (+)
  mult' = (*)

-- add vectors
infixl 3 -+- 
(-+-) : (Num' t) => V.Vect n t -> V.Vect n t -> V.Vect n t
(-+-) = V.zipWith add'

-- multply vectors
infixl 8 -*- 
(-*-) : (Num' t) => V.Vect n t -> V.Vect n t -> V.Vect n t
(-*-) = V.zipWith mult'

%overlapping
(Num' t) => Num' (V.Vect n t) where
  add'  = (-+-)
  mult' = (-*-)

-- Dot Product  
infixl 8 |.|
(|.|) : (Num' t) => V.Vect (S n) t -> V.Vect (S n) t -> t
(|.|) v1 v2 = V.foldl1 mult' $ v1 -*- v2

-- Matrix type
Matrix : (t : Type) -> (n : Nat) -> (m: Nat) -> Type
Matrix a n m = V.Vect n (V.Vect m a)  

parameters (t : Type, isNum' : Num' t)

  -- Matrices viewed as Linear transformations
  infixr 9 ~>
  (~>) : Nat -> Nat -> Type
  (~>) n m = Matrix t n m 

  -- Transpose viewed as a contravariant Functor 
  contraF : (n ~> m) -> (m ~> n)
  contraF = V.transpose
  
  Iso_ContraF : (mat : (n ~> m)) -> ((contraF . contraF $ mat) = mat)
  Iso_ContraF m = ?Proof1

  -- Construct Matricies longituitly
  infixl 9 <->
  (<->) : (m ~> n) -> (m ~> n') -> (m ~> (n + n'))
  (<->) m1 m2 = contraF $ (contraF m1) ++ (contraF m2)

  -- Linear Transformation composition via Matrix multiplication
  infixl 7 |. 
  (|.) : (a ~> b) -> (b ~> c) -> (a ~> c)
  (|.) m1 m2 = ?compose
