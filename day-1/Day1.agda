
module Day1 where


open import Data.String as String
open import Data.Maybe
open import Foreign.Haskell using (Unit)
open import Data.List as List
open import Data.Nat
import Data.Nat.Show as ℕs
open import Data.Char
open import Data.Vec as Vec renaming (_>>=_ to _VV=_ ; toList to VecToList)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Nat.Properties
open import Data.Bool.Base
open import AocIO
open import AocUtil
open import AocVec

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

main2 : IO Unit
main2 = mainBuilder (readFileMain processFile)
     where
       processDigits : {M : ℕ} → Vec ℕ M → IO Unit
       processDigits vs with (neighbours vs)
       ... | neigh with (onlyKeepPairs (VecToList neigh))
       ... | pairs with (List.map  Σ.proj₁ pairs)
       ... | nums = putStrLn (toCostring (ℕs.show (List.sum nums)))
       processLine : List Char → IO Unit
       processLine ls with (parseDigits ls)
       ... | nothing = putStrLn (toCostring ("Failed to parse this line: " String.++ (String.fromList ls)))
       ... | just digs = processDigits (Vec.fromList digs)
       processFile : String → IO Unit
       processFile file-content with (lines (String.toList file-content))
       ... | file-lines with (List.map processLine file-lines)
       ... | ops = void (sequence-io-prim ops)

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
      processDigits : {N : ℕ} → Vec ℕ N → IO Unit
      processDigits vs with (checkEvenVec vs)
      ... | nothing = printString "Input has to have even length"
      ... | just (M , p) with (halfwayNeighbours M v)
        where
          v : Vec ℕ (M + M)
          v rewrite p = vs
      ... | half-neigh with (onlyKeepPairs (VecToList half-neigh))
      ... | pairs with (List.map Σ.proj₁ pairs)
      ... | nums = printString (ℕs.show (List.sum nums))
      processLine : List Char → IO Unit
      processLine ls with (parseDigits ls)
      ... | nothing = putStrLn (toCostring ("Failed to parse this line: " String.++ (String.fromList ls)))
      ... | just digs = processDigits (Vec.fromList digs)
      processFile : String → IO Unit
      processFile file-content with (lines (String.toList file-content))
      ... | file-lines with (List.map processLine file-lines)
      ... | ops = void (sequence-io-prim ops)

