module plfa.part1.Naturals where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
--a + zero = a
--a + suc b = suc (a + b)
zero + b = b
suc a + b = suc (a + b)

_*_ : ℕ → ℕ → ℕ
a * zero = zero
a * suc b = a + (a * b)

_**_ : ℕ → ℕ → ℕ
a ** zero = suc zero
a ** suc b = a * (a ** b)

_***_ : ℕ → ℕ → ℕ
a *** zero = suc zero
a *** suc b = a ** (a *** b) 

_∸_ : ℕ → ℕ → ℕ
a ∸ zero = a
zero ∸ (suc b) = zero
(suc a) ∸ (suc b) = a ∸ b

infixl 6  _+_  _∸_
infixl 7  _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

_ : 3 ∸ 2 ≡ 1
_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

_ : 2 ∸ 3 ≡ 0
_ =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎


_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc 4))
  ≡⟨⟩
    suc (suc 5)
  ≡⟨⟩
    suc 6
  ≡⟨⟩
    7
  ∎    

_ : 2 * 3 ≡ 6
_ =
  begin
    2 * 3
  ≡⟨⟩    -- inductive case
    3 + (1 * 3)
  ≡⟨⟩    -- inductive case
    3 + (3 + (0 * 3))
  ≡⟨⟩    -- base case
    3 + (3 + 0)
  ≡⟨⟩    -- simplify
    6
  ∎

_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    12
  ∎

_ : 3 * 0 ≡ 0
_ = refl

_ : 0 * 3 ≡ 0
_ = refl


_ : 3 + 0 ≡ 3
_ =
  begin
    3 + 0
  ≡⟨⟩
    suc (2 + 0)
  ≡⟨⟩
    suc (suc (1 + 0))
  ≡⟨⟩
    suc (suc (suc (0 + 0)))
  ≡⟨⟩
    suc (suc (suc 0))
  ≡⟨⟩
    3
  ∎

