module EvenOdd where

open import Data.Nat

data Even : ℕ → Set where
  evenZero : Even 0
  evenSuc : {n : ℕ} → Even n → Even (suc (suc n))

data Odd : ℕ → Set where
  oddOne : Odd 1
  oddSuc : {n : ℕ} → Odd n → Odd (suc (suc n))

_e+e_ : {n m : ℕ} → Even n → Even m → Even (n + m)
evenZero e+e b = b
evenSuc a e+e b = evenSuc (a e+e b)

_o+o_ : {n m : ℕ} → Odd n → Odd m → Even (n + m)
oddOne o+o oddOne = evenSuc evenZero
oddOne o+o oddSuc b = evenSuc (oddOne o+o b)
oddSuc a o+o b = evenSuc (a o+o b)

_o+e_ : {n m : ℕ} → Odd n → Even m → Odd (n + m)
oddOne o+e evenZero = oddOne
oddOne o+e evenSuc b = oddSuc (oddOne o+e b)
oddSuc a o+e b = oddSuc (a o+e b)

_e+o_ : {n m : ℕ} → Even n → Odd m → Odd (n + m)
evenZero e+o b = b
evenSuc a e+o b = oddSuc (a e+o b)
