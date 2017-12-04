
module Day2 where


open import Data.String as String
open import Data.Maybe
open import Foreign.Haskell using (Unit)
open import Data.List as List hiding (fromMaybe)
open import Data.Nat
open import Data.Nat.DivMod
import Data.Nat.Show as ℕs
open import Data.Char
open import Data.Vec as Vec renaming (_>>=_ to _VV=_ ; toList to VecToList)
open import Data.Product
open import Relation.Nullary
open import Data.Nat.Properties
open import Data.Bool.Base
open import AocIO
open import AocUtil
open import AocVec
import Data.Fin as Fin

words : List Char → List (List Char)
words = splitWhen isWhitespace
  where
    isWhitespace : Char → Bool
    isWhitespace ' ' = true
    isWhitespace '\t' = true
    isWhitespace _ = false

unsafeParseInt : List Char → ℕ
unsafeParseInt ls = unsafeParseInt' 0 ls
  where
    unsafeParseInt' : ℕ → List Char → ℕ
    unsafeParseInt' acc [] = acc
    unsafeParseInt' acc (x ∷ ls) with (toDigit x)
    ... | nothing = acc * 10
    ... | just n = unsafeParseInt' (n + (acc * 10)) ls

natDiff : ℕ → ℕ → ℕ
natDiff zero y = y
natDiff x zero = x
natDiff (suc x) (suc y) = natDiff x y

fromMaybe :  ∀ {a} {A : Set a} → A → Maybe A → A
fromMaybe v (just x) = x
fromMaybe v nothing = v

find : ∀ {a} {A : Set a} → (A → Bool) → List A → Maybe A
find pred [] = nothing
find pred (x ∷ ls) with (pred x)
... | false = find pred ls
... | true = just x

dividesEvenly : ℕ → ℕ → Bool
dividesEvenly zero zero = true
dividesEvenly zero dividend = false
dividesEvenly (suc divisor) dividend with (dividend mod (suc divisor))
... | Fin.Fin.zero = true
... | Fin.Fin.suc p = false

oneDividesTheOther : ℕ → ℕ → Bool
oneDividesTheOther x y = dividesEvenly x y ∨ dividesEvenly y x

main2 : IO Unit
main2 = mainBuilder (readFileMain processFile)
  where
    parseLine : List Char → List ℕ
    parseLine ls with (words ls)
    ... | line-words = List.map unsafeParseInt line-words
    minMax : {n : ℕ} → Vec ℕ (suc n) → (ℕ × ℕ)
    minMax {0} (x ∷ []) = x , x
    minMax {suc _} (x ∷ ls) with (minMax ls)
    ... | min , max = (min ⊓ x) , (max ⊔ x)
    minMaxDiff : List ℕ → ℕ
    minMaxDiff ls = helper (Vec.fromList ls)
      where
        helper : {n : ℕ} → Vec ℕ n → ℕ
        helper [] = 0
        helper (x ∷ vec) with (minMax (x ∷ vec))
        ... | min , max = natDiff min max
    lineDiff : List Char → ℕ
    lineDiff s = minMaxDiff (parseLine s)
    processFile : String → IO Unit
    processFile file-content with (lines (String.toList file-content))
    ... | file-lines with (List.map lineDiff file-lines)
    ... | line-diffs = printString (ℕs.show (List.sum line-diffs))

main : IO Unit
main = mainBuilder (readFileMain processFile)
  where
    parseLine : List Char → List ℕ
    parseLine ls with (words ls)
    ... | line-words = List.map unsafeParseInt line-words
    pierreDiv : ℕ → ℕ → ℕ
    pierreDiv x y with (x ⊓ y) | (x ⊔ y)
    ... | 0 | _ = 0
    ... | _ | 0 = 0
    ... | (suc min) | (suc max) = (suc max) div (suc min)
    lineDivider : List ℕ → Maybe ℕ
    lineDivider [] = nothing
    lineDivider (x ∷ ln) with (find (oneDividesTheOther x) ln)
    ... | nothing = lineDivider ln
    ... | just y = just (pierreDiv x y)
    lineScore : List Char → ℕ
    lineScore s = fromMaybe 0 (lineDivider (parseLine s))
    processFile : String → IO Unit
    processFile file-content with (lines (String.toList file-content))
    ... | file-lines with (List.map lineScore file-lines)
    ... | line-scores = printString (ℕs.show (List.sum line-scores))
