module AocVec where
open import Data.Vec as Vec
open import Data.Nat

addToBack : {A : Set} → {N : ℕ} → A → Vec A N → Vec A (suc N)
addToBack v [] = v ∷ []
addToBack v (x ∷ vs) = x ∷ addToBack v vs

dupFrontToBack : {A : Set} → {N : ℕ} → Vec A (suc N) → Vec A (suc (suc N))
dupFrontToBack (x ∷ vs) = addToBack x (x ∷ vs)

dupFirstNToBack : {A : Set} → {M : ℕ} → (N : ℕ) → Vec A (suc M) → Vec A (N + (suc M))
dupFirstNToBack zero vs = vs
dupFirstNToBack (suc N) (x ∷ vs) = x ∷ dupFirstNToBack N (addToBack x vs)