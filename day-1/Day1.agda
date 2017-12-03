
module Day1 where


open import Data.String as String
open import Data.Maybe
open import Foreign.Haskell using (Unit)
open import IO.Primitive
open import Data.List as List
open import Data.Nat
import Data.Nat.Show as ℕs
open import Data.Char
open import Data.Vec as Vec renaming (_>>=_ to _VV=_ ; toList to VecToList)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Nat.Properties

postulate
  getLine : IO Costring

{-# COMPILE GHC getLine = getLine #-}

{-# FOREIGN GHC import qualified Data.Text    as Text #-}
{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# FOREIGN GHC import System.Environment (getArgs, getProgName) #-}

postulate
  getArgs : IO (List String)
  getProgName : IO String

{-# COMPILE GHC getArgs = fmap (map Text.pack) getArgs #-}
{-# COMPILE GHC getProgName = fmap Text.pack getProgName   #-}

toDigit : Char → Maybe ℕ
toDigit '0' = just 0
toDigit '1' = just 1
toDigit '2' = just 2
toDigit '3' = just 3
toDigit '4' = just 4
toDigit '5' = just 5
toDigit '6' = just 6
toDigit '7' = just 7
toDigit '8' = just 8
toDigit '9' = just 9
toDigit _ = nothing

addToBack : {A : Set} → {N : ℕ} → A → Vec A N → Vec A (suc N)
addToBack v [] = v ∷ []
addToBack v (x ∷ vs) = x ∷ addToBack v vs

dupFrontToBack : {A : Set} → {N : ℕ} → Vec A (suc N) → Vec A (suc (suc N))
dupFrontToBack (x ∷ vs) = addToBack x (x ∷ vs)

dupFirstNToBack : {A : Set} → {M : ℕ} → (N : ℕ) → Vec A (suc M) → Vec A (N + (suc M))
dupFirstNToBack zero vs = vs
dupFirstNToBack (suc N) (x ∷ vs) = x ∷ dupFirstNToBack N (addToBack x vs)

makePairs : {A : Set} → {N : ℕ } → Vec A (suc N) → Vec (A × A) N
makePairs (x ∷ y ∷ vs) = ( ( x , y )) ∷ makePairs (y ∷ vs)
makePairs (x ∷ []) = []

-- vecLength : {A : Set} → (N M : ℕ) → Vec A (N + M) → Vec A (M + N)
-- vecLength N M vs rewrite (+-comm M N) = vs

makeNPairs : {A : Set} → {M : ℕ} → (N : ℕ) → Vec A (N + M) → Vec (A × A) M
makeNPairs {M = M} N vs with (Vec.drop N vs)
... | ends rewrite (+-comm N M) with (Vec.take M vs)
... | starts =  Vec.zip starts ends

neighbours : {A : Set} → {N : ℕ} → Vec A N → Vec (A × A) N
neighbours [] = []
neighbours (x ∷ vs) with (dupFrontToBack (x ∷ vs))
... | dvs = makePairs dvs

halfwayNeighbours : {A : Set} → (N : ℕ) → Vec A (N + N) → Vec (A × A) (N + N)
halfwayNeighbours 0 [] = []
halfwayNeighbours (suc N) v with (dupFirstNToBack (suc N) v)
... | dupped with (makeNPairs (suc N) dupped)
... | pairs = pairs

parseDigits : List Char → Maybe (List ℕ)
parseDigits [] = Maybe.just []
parseDigits (c ∷ cs) with (toDigit c) | (parseDigits cs)
...                                    | (just n)   | (just ns) = just (n ∷ ns)
...                                    | _            | _             = nothing

onlyKeepPairs : List (ℕ × ℕ) → List (ℕ × ℕ)
onlyKeepPairs [] = []
onlyKeepPairs ((a , b) ∷ xs) with (a Data.Nat.≟ b)
... | yes p = (a , b) ∷ onlyKeepPairs xs
... | no ¬p = onlyKeepPairs xs

main2 : IO Unit
main2 = getProgName >>= λ name →
                   getArgs >>= λ args →  main' name args
     where
       processFile : String → IO Unit
       processFile fs with (parseDigits (toList fs) )
       ... | nothing = putStrLn (toCostring "Failed to parse file")
       ... | (just digs) with (VecToList (neighbours (Vec.fromList digs)))
       ... | neigh with (onlyKeepPairs neigh)
       ... | pairs with (List.foldr (λ pair acc → acc +  Σ.proj₁ pair ) 0 pairs)
       ... | sum = putStrLn (toCostring (ℕs.show sum))
       main' : String → (List String) → IO Unit
       main' name (file ∷ []) = readFiniteFile file >>= processFile
       main' name _ = putStrLn (toCostring ("Usage: " String.++ name String.++ " FILE"))

vecLength : ∀ {a} → {A : Set a} → {n : ℕ} → Vec A n → ℕ
vecLength [] = 0
vecLength (x ∷ vs) = suc (vecLength vs)

main : IO Unit
main = getProgName >>= λ name →
                    getArgs >>= λ args →  main' name args
      where
        processFile : String → IO Unit
        processFile fs with (parseDigits (toList fs) )
        ... | nothing = putStrLn (toCostring "Failed to parse file")
        ... | (just digs) with (Vec.fromList digs)
        ... | x with (vecLength x)
        ... | vl = {!checkEvenVec digs x!}
        main' : String → (List String) → IO Unit
        main' name (file ∷ []) = readFiniteFile file >>= processFile
        main' name _ = putStrLn (toCostring ("Usage: " String.++ name String.++ " FILE"))

