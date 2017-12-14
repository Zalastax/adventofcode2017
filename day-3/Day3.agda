
module Day3 where


open import Data.String as String
open import Data.Maybe
open import Foreign.Haskell using (Unit)
open import Data.List as List hiding (fromMaybe)
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties
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
open import Relation.Binary.PropositionalEquality
open import EvenOdd

printUsage : String → IO Unit
printUsage name = printString ("Usage: " String.++ name String.++ " NUMBER\n(NUMBER > 0)")

sqr : (l : ℕ) → Σ[ k ∈ ℕ ] (k ≡ l * l)
sqr l = l * l , refl


first-larger-odd-square : {m : ℕ} → (n : ℕ) → suc m ≡ n → Σ[ k ∈ ℕ ] (n ≤ (k * k) × Odd k)
first-larger-odd-square {m} n n-is-suc = helper 1 m n-is-suc oddOne
  where
    helper : (m diff : ℕ) → (m + diff) ≡ n → Odd m → Σ[ k ∈ ℕ ] (n ≤ (k * k) × Odd k)
    helper m (suc (suc diff)) p m-is-odd with sqr m
    ... | (m² , m²≡m*m) with n ≤? m²
    ... | yes n≤m² rewrite m²≡m*m = m , n≤m² , m-is-odd
    ... | no _ = helper (suc (suc m)) diff rewr-p (oddSuc m-is-odd)
      where
        rewr-p : suc (suc m + diff) ≡ n
        rewr-p with (+-suc m diff) | (+-suc m (suc diff))
        ... | s | t rewrite (sym s) | t = p
    helper m zero p m-is-odd rewrite (+-identityʳ m) with (sqr m)
    ... | (m² , q) = m , (my-proof n refl) , m-is-odd
      where
        my-proof : (k : ℕ) → k ≡ n → n ≤ m * m
        my-proof k p₁ rewrite sym p₁ with k
        ... | zero = z≤n
        ... | suc kk rewrite p with (m≤m+n kk (kk * suc kk))
        ... | kk≤kk+junk = s≤s kk≤kk+junk
    helper zero (suc zero) p ()
    helper (suc zero) (suc zero) p m-is-odd rewrite sym p = 3 , (s≤s (s≤s z≤n) , oddSuc oddOne)
    helper (suc (suc m)) (suc zero) p m-is-odd = (suc (suc m)) , my-proof n refl , m-is-odd
      where
        my-proof : (k : ℕ) → k ≡ n → n ≤ suc (suc (m + suc (suc (m + m * suc (suc m)))))
        my-proof k p₁ rewrite sym p₁ with k
        ... | zero = z≤n
        -- we replace with p and get an expression 1 + m ≤ suc (suc m + junk)
        -- +-comm m 1 turns 1 + m into suc m
        -- sym +-suc turns m + suc junk into suc (m + junk) to match the number on the other side
        -- finally we cancel suc on both sides and use m ≤ m + junk
        ... | suc kk rewrite sym p | +-comm m 1 | +-suc m (suc (m + m * suc (suc m))) = s≤s (s≤s (s≤s (m≤m+n m (suc (m + m * suc (suc m))))))

oddness : ∀ {n} → Odd n → ℕ
oddness oddOne = 1
oddness (oddSuc v) = suc (oddness v)

ring-for-square# : {m : ℕ} → (n : ℕ) → suc m ≡ n → Σ[ k ∈ ℕ ] Odd k × ℕ
ring-for-square# zero ()
ring-for-square# (suc n) p with (first-larger-odd-square (suc n) (cong suc refl))
... | k , proj₄ , k-odd = k , k-odd , (oddness k-odd)

ring-corners : {m : ℕ} → Odd m → ℕ × ℕ × ℕ × ℕ × ℕ
ring-corners oddOne = 1 , (1 , (1 , 1 , 1))
ring-corners {(suc (suc n))} (oddSuc _)  = (n * n) , ((proj₁ first-corner) , ((proj₁ second-corner) , ((proj₁ third-corner) , (proj₁ fourth-corner))))
  where
    first-corner : Σ[ k ∈ ℕ ] k ≡ suc ((n * n) + n)
    first-corner = suc (n * n + n) , refl
    second-corner : Σ[ k ∈ ℕ ] k ≡ suc (suc ((n * n) + n + n))
    second-corner = (suc (suc (n * n + n + n))) , refl
    third-corner : Σ[ k ∈ ℕ ] k ≡ suc (suc (suc ((n * n) + n + n + n)))
    third-corner = suc (suc (suc (n * n + n + n + n))) , refl
    fourth-corner : Σ[ k ∈ ℕ ] k ≡ suc (suc (n + suc (suc (n + n * suc (suc n)))))
    fourth-corner = sqr (suc (suc n))
    ring-length : Σ[ k ∈ ℕ ] k ≡ (2 * (suc (suc n))) + (2 * n)
    ring-length = (2 * (suc (suc n)) + 2 * n) , refl
    -- proof that fourth-corner = ring-length + prev-fourth-corner
    ring-length-proof : {m l : ℕ} → m ≡ suc (suc (n + suc (suc (n + n * suc (suc n))))) → l ≡ (2 * (suc (suc n))) + (2 * n) →  l + (n * n) ≡ m
    ring-length-proof p q rewrite p | q = cong suc (cong suc my-proof)
      where
        halp : n + n + (n + n) ≡ n + n + n + n
        halp = begin
           n + n + (n + n)
           ≡⟨ sym (+-assoc (n + n) n n) ⟩
           n + n + n + n ∎
          where
            open ≡-Reasoning
        halp-again : n * n + (n + n + n + n) ≡ n * n + n + n + n + n
        halp-again with +-assoc (n * n) (n + n + n) n
        ... | p₁  rewrite sym p₁ with +-assoc (n * n) (n + n) n
        ... | p₂ rewrite sym p₂ with +-assoc (n * n) n n
        ... | p₃ rewrite sym p₃ = refl
        my-proof : n + suc (suc (n + 0)) + (n + (n + 0)) + n * n ≡ n + suc (suc (n + n * suc (suc n)))
        my-proof rewrite +-identityʳ n | +-*-suc n (suc n) | +-*-suc n n with +-comm n (suc (suc n)) | +-comm n (suc (suc (n + (n + (n + n * n)))))
        ... | p₁ | p₂ rewrite p₁ | p₂ with +-comm n (n + n * n) | +-comm n (n + n * n + n) | +-comm n (n * n) | +-comm (n + n + (n + n)) (n * n)
        ... | p₃ | p₄ | p₅ | p₆ rewrite p₃ | p₄ | p₅ | p₆ | halp | halp-again = cong suc (cong suc refl)
    -- Here I'd like a proof that the distance between the corners add up to the length

abs-diff : (n m : ℕ) → ℕ
abs-diff zero m = m
abs-diff (suc n) zero = suc n
abs-diff (suc n) (suc m) = abs-diff n m

min-5 : (a b c d e : ℕ) → ℕ
min-5 a b c d e with a ⊓ b | c ⊓ d
... | min-ab | min-cd with min-ab ⊓ min-cd
... | min-abcd = min-abcd ⊓ e

dist-to-closest-ring-corner : {k : ℕ} → (n : ℕ) → suc k ≡ n → ℕ
dist-to-closest-ring-corner zero ()
dist-to-closest-ring-corner (suc k) p with (ring-for-square# (suc k) p) | (suc k)
... | corner-root , corner-root-odd , ring# | n with ring-corners corner-root-odd
... | c₀ , c₁ , c₂ , c₃ , c₄ with abs-diff n c₀ | abs-diff n c₁ | abs-diff n c₂ | abs-diff n c₃ | abs-diff n c₄
... | n-c₀ | n-c₁ | n-c₂ | n-c₃ | n-c₄ = min-5 n-c₀ n-c₁ n-c₂ n-c₃ n-c₄

dist-to-center : {k : ℕ} → (n : ℕ) → suc k ≡ n → ℕ
dist-to-center zero ()
dist-to-center (suc k) p with (ring-for-square# (suc k) p) | (suc k)
... | corner-root , corner-root-odd , ring# | n with dist-to-closest-ring-corner (suc k) refl
... | dist = abs-diff dist (2 * (pred ring#))

infixr 5 _+++_

_+++_ : String → String → String
_+++_ s1 s2 = s1 String.++ " " String.++ s2

print-corners : {k : ℕ} → (n : ℕ) → suc k ≡ n → IO Unit
print-corners zero ()
print-corners (suc k) p with (ring-for-square# (suc k) p) | (suc k)
... | corner-root , corner-root-odd , ring# | n with ring-corners corner-root-odd
... | c₀ , c₁ , c₂ , c₃ , c₄ with abs-diff n c₀ | abs-diff n c₁ | abs-diff n c₂ | abs-diff n c₃ | abs-diff n c₄
... | n-c₀ | n-c₁ | n-c₂ | n-c₃ | n-c₄ with ℕs.show n-c₀ | ℕs.show n-c₁ | ℕs.show n-c₂ | ℕs.show n-c₃ | ℕs.show n-c₄ | ℕs.show corner-root | ℕs.show ring#
... | s0 | s1 | s2 | s3 | s4 | s5 | s6 = printString (s0 +++ s1 +++ s2 +++ s3 +++ s4 +++ "==" +++ s5 +++ s6)

main : IO Unit
main = mainBuilder main'
  where
    main' : String → (List String) → IO Unit
    main' name (numS ∷ []) with (unsafeParseNat (String.toList numS))
    ... | 0 = printUsage name
    ... | (suc n) =  printString (ℕs.show (dist-to-center (suc n) (cong suc refl)))
    main' name _ = printUsage name
