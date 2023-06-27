{-# OPTIONS --universe-polymorphism #-}
module moore where

open import Data.List
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Agda.Primitive

infix 4 _≡≡_

-- Type constructor for functional equality
_≡≡_ : ∀{A B : Set} ->  (A -> B) -> (A -> B) -> Set
_≡≡_ {A} {B} f g = ∀(x : A) -> f x ≡ g x

-- Function extensionality
postulate
   funext : {A B : Set} {f g : A -> B} -> f ≡≡ g -> f ≡ g

-- The Structured Input, Structured Output type
data SISO : Set -> Set -> Set where
  siso : {a b : Set} -> (List a -> b) -> SISO a b

-- The Moore type
data Moore : Set -> Set -> Set where
  moore : {a b : Set} -> b -> (a -> Moore a b) -> Moore a b

-- Moore monoidal profunctor multiplication
_>***<_ : {a b c d : Set} -> Moore a b -> Moore c d -> Moore (a × c) (b × d)
moore x x₁ >***< moore y x₃ = moore (x , y) λ(a , c) -> x₁ a >***< x₃ c

-- SISO monoidal profunctor multiplication
_***_ : {a b c d : Set } -> SISO a b -> SISO c d -> SISO (a × c) (b × d)
siso x *** siso y = siso (λ ls -> let (les , res) = unzip ls in (x les , y res) )

-- Profunctor instance
record Profunctor (p : Set -> Set -> Set) : Set₁ where
   field
       dimap : {a b c d : Set} -> (a -> b) -> (c -> d) -> p b c -> p a d

mooreProf : Profunctor Moore
mooreProf = {!!}

-- Running a Moore machine
runMooref : {a b : Set} ->  Moore a b -> List a -> b
runMooref (moore x x₁) [] = x
runMooref (moore x f) (l ∷ ls) = runMooref (f l) ls

-- The fold function using the Moore-SISO natural transformation
mfoldl : {a b : Set} -> Moore a b -> SISO a b
mfoldl m = siso (λ ls -> runMooref m ls)

-- This is just the map function
_<$>_ : {A B : Set} -> (A -> B) -> List A -> List B
f <$> ls = Data.List.map f ls

-- This lemma serves as a readability aid by employing function extensionality 
-- on a polymorphic list. Our strategy is straightforward: we perform structural 
-- induction on the Moore type.
helper : {a b c d : Set}(m : Moore a b)(n : Moore c d)
         -> (λ ls -> runMooref (m >***< n) ls) ≡≡ (λ ls -> ((runMooref m (proj₁ (unzip ls))) , (runMooref n (proj₂ (unzip ls)))))
helper (moore x _) (moore y _) [] = refl
helper (moore _ am) (moore _ bm) (x ∷ zs) = helper (am (proj₁ x)) (bm (proj₂ x)) zs

-- This lemma, referred to as Lemma 6 in the accompanying text, asserts that the
-- function mfoldl preserves the structure of the monoidal multiplication. To enhance
-- readability and clarity of our code, we employ the above helper function in the proof of this lemma.
lemma3 : {a b c d : Set}(m : Moore a b)(n : Moore c d) -> mfoldl (m >***< n) ≡ mfoldl m *** mfoldl n
lemma3 m n = cong siso (funext (helper m n))


