
module Day5 where


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
open import Prelude.Int

unsafeParseInt : List Char → Int
unsafeParseInt ('-' ∷ ls) with (unsafeParseNat ls)
... | zero = pos zero
... | suc n = negsuc n
unsafeParseInt ls = pos (unsafeParseNat ls)


main : IO Unit
main = mainBuilder (readFileMain process-file)
  where
    process-file : String → IO Unit
    process-file file-content with lines (unpackString file-content)
    ... | file-lines with List.map unsafeParseInt file-lines
    ... | instructions with List.map (λ n → printString (primShowInteger n)) instructions
    ... | io-ops = void (sequence-io-prim io-ops)

