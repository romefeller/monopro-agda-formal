{-# OPTIONS --universe-polymorphism #-}
module moore where

open import Data.List
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Agda.Primitive

infix 4 _≡≡_

_≡≡_ : ∀{A B : Set} ->  (A -> B) -> (A -> B) -> Set
_≡≡_ {A} {B} f g = ∀(x : A) -> f x ≡ g x

postulate
   funext : {A B : Set} {f g : A -> B} -> f ≡≡ g -> f ≡ g

data SISO : Set -> Set -> Set where
  siso : {a b : Set} -> (List a -> b) -> SISO a b

data Moore : Set -> Set -> Set where
  moore : {a b : Set} -> b -> (a -> Moore a b) -> Moore a b

_>***<_ : {a b c d : Set} -> Moore a b -> Moore c d -> Moore (a × c) (b × d)
moore x x₁ >***< moore y x₃ = moore (x , y) λ(a , c) -> x₁ a >***< x₃ c

_***_ : {a b c d : Set } -> SISO a b -> SISO c d -> SISO (a × c) (b × d)
siso x *** siso y = siso (λ ls -> let (les , res) = unzip ls in (x les , y res) )

record Profunctor (p : Set -> Set -> Set) : Set₁ where
   field
       dimap : {a b c d : Set} -> (a -> b) -> (c -> d) -> p b c -> p a d

mooreProf : Profunctor Moore
mooreProf = {!!}

runMooref : {a b : Set} ->  Moore a b -> List a -> b
runMooref (moore x x₁) [] = x
runMooref (moore x f) (l ∷ ls) = runMooref (f l) ls

mfoldl : {a b : Set} -> Moore a b -> SISO a b
mfoldl m = siso (λ ls -> runMooref m ls)

_<$>_ : {A B : Set} -> (A -> B) -> List A -> List B
f <$> ls = Data.List.map f ls

helper : {a b c d : Set}(m : Moore a b)(n : Moore c d)
         -> (λ ls -> runMooref (m >***< n) ls) ≡≡ (λ ls -> ((runMooref m (proj₁ (unzip ls))) , (runMooref n (proj₂ (unzip ls)))))
helper (moore x _) (moore y _) [] = refl
helper (moore _ am) (moore _ bm) (x ∷ zs) = helper (am (proj₁ x)) (bm (proj₂ x)) zs

propMult : {a b c d : Set}(m : Moore a b)(n : Moore c d) -> mfoldl (m >***< n) ≡ mfoldl m *** mfoldl n
propMult m n = cong siso (funext (helper m n))


