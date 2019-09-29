module binary where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

{-# BUILTIN NATURAL ℕ #-}

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc x) = inc (to x)

from : Bin → ℕ
from ⟨⟩ = zero
from (x O) = (from x) * 2
from (x I) = ((from x) * 2) + 1

_ : to 23 ≡ ⟨⟩ I O I I I
_ = refl

_ : from (⟨⟩ I O I I I) ≡ 23
_ = refl

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ =
  begin
    inc (⟨⟩ I O I I)
  ≡⟨⟩
    (inc (⟨⟩ I O I)) O
  ≡⟨⟩
    (inc (⟨⟩ I O)) O O
  ≡⟨⟩
    (⟨⟩ I I) O O
  ≡⟨⟩
    ⟨⟩ I I O O
  ∎
