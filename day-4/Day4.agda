
module Day4 where


open import Prelude.String as String
open import Data.Maybe
open import Foreign.Haskell using (Unit)
open import Prelude.List as List
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties
import Data.Nat.Show as ℕs
open import Prelude.Char
open import Data.Vec as Vec renaming (_>>=_ to _VV=_ ; toList to VecToList)
open import Data.Product
open import Relation.Nullary
open import Data.Nat.Properties
open import Data.Bool.Base
open import AocIO
open import AocUtil
open import AocVec
open import Relation.Binary.PropositionalEquality
open import EvenOdd

count-falsy : List Bool → ℕ
count-falsy ls = length (filter not ls)

split-line : List Char → List String
split-line ls with (words ls)
... | ls-words = List.map packString ls-words

has-following-duplicates : List String → Bool
has-following-duplicates [] = false
has-following-duplicates (x ∷ []) = false
has-following-duplicates (x ∷ y ∷ ls) with primStringEquality x y
... | false = has-following-duplicates (y ∷ ls)
... | true = true


main : IO Unit
main = mainBuilder (readFileMain process-file)
  where
    sort-word : String → String
    sort-word s with unpackString s
    ... | ls with sort ls
    ... | ls-sorted = packString ls-sorted
    is-valid-passphrase : List String → Bool
    is-valid-passphrase ls with List.map sort-word ls
    ... | sorted-words with sort sorted-words
    ... | ls-sorted = has-following-duplicates ls-sorted
    process-file : String → IO Unit
    process-file file-content with (lines (unpackString file-content))
    ... | file-lines with (List.map split-line file-lines)
    ... | lines-split-into-words with (List.map is-valid-passphrase lines-split-into-words)
    ... | lines-are-valid with count-falsy lines-are-valid
    ... | valid-count = printString (ℕs.show valid-count)

main2 : IO Unit
main2 = mainBuilder (readFileMain process-file)
  where
    is-valid-passphrase : List String → Bool
    is-valid-passphrase ls with sort ls
    ... | ls-sorted = has-following-duplicates ls-sorted
    process-file : String → IO Unit
    process-file file-content with (lines (unpackString file-content))
    ... | file-lines with (List.map split-line file-lines)
    ... | lines-split-into-words with (List.map is-valid-passphrase lines-split-into-words)
    ... | lines-are-valid with count-falsy lines-are-valid
    ... | valid-count = printString (ℕs.show valid-count)
