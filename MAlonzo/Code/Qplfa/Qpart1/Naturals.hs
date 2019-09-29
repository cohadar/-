{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Qplfa.Qpart1.Naturals where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

name6 = "plfa.part1.Naturals.ℕ"
d6 = ()
data T6 = C8 | C10 T6
name12 = "plfa.part1.Naturals._+_"
d12 :: T6 -> T6 -> T6
d12 v0 v1
  = case coe v0 of
      C8 -> coe v1
      C10 v2 -> coe (C10 (coe (d12 (coe v2) (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
