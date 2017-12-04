
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
open import AocIO

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

mainBuilder : (String → (List String) → IO Unit) → IO Unit
mainBuilder main' = getProgName >>= λ name → getArgs >>= main' name

readFileMain : (String → IO Unit) → String → (List String) → IO Unit
readFileMain f name (file ∷ []) = readFiniteFile file >>= f
readFileMain f name _ = putStrLn (toCostring ("Usage: " String.++ name String.++ " FILE"))

main2 : IO Unit
main2 = mainBuilder (readFileMain processFile)
     where
       processFile : String → IO Unit
       processFile fs with (parseDigits (toList fs) )
       ... | nothing = putStrLn (toCostring "Failed to parse file")
       ... | (just digs) with (VecToList (neighbours (Vec.fromList digs)))
       ... | neigh with (onlyKeepPairs neigh)
       ... | pairs with (List.foldr (λ pair acc → acc +  Σ.proj₁ pair ) 0 pairs)
       ... | sum = putStrLn (toCostring (ℕs.show sum))

checkEvenVec : ∀ {a} {A : Set a} → {N : ℕ} → Vec A N → Maybe (Σ[ M ∈ ℕ ] M + M ≡ N)
checkEvenVec [] = just (0 , refl)
checkEvenVec (x ∷ []) = nothing
checkEvenVec { N = N} (x ∷ y ∷ vs) with (checkEvenVec vs)
... | nothing = nothing
... | just (M , p) with (cong suc (+-suc M M))
... | t rewrite p = just ((suc M) , t)

main : IO Unit
main = mainBuilder (readFileMain processFile)
      where
        processFile : String → IO Unit
        processFile fs with (parseDigits (toList fs) )
        ... | nothing = putStrLn (toCostring "Failed to parse file")
        ... | (just digs) with (Vec.fromList digs)
        ... | digsv with (checkEvenVec digsv)
        ... | nothing = putStrLn (toCostring "Input has to have even length")
        ... | just (M , p) rewrite p with (halfwayNeighbours M v)
          where
            v : Vec ℕ (M + M)
            v rewrite p = digsv
        ... | hn with (onlyKeepPairs (VecToList hn) )
        ... | pairs with (List.foldr (λ pair acc → acc + Σ.proj₁ pair) 0 pairs)
        ... | sum = putStrLn (toCostring (ℕs.show sum))

