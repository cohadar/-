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
