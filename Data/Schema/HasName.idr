||| Proof that a Schema has a specificly named element.
|||
module Data.Schema.HasName

import Data.Schema.Restricted
import Data.Schema


public export
data HasName : (name : n) -> (schema : Schema n b) -> Type where
  IsSimple : (prf : a = b)
                 -> HasName a (Simple (MkAtom b ty r p))

  IsComplex : (prf : a = b)
                  -> HasName a (Complex b rest)

  StepEat : (prf : HasName a this)
                -> HasName a (SeqEat this later)

  StepEmp : (prf : HasName a this)
                -> HasName a (SeqEmpty this later)

  StepAlongEat : (prf  : Not (HasName a         this))
              -> (step :      HasName a              later)
                      ->      HasName a (SeqEat this later)

  StepAlongEmp : (prf  : Not (HasName a this))
              -> (step :      HasName a                later)
                      ->      HasName a (SeqEmpty this later)

  StepLeft : (prf  : Not (HasName a r))
          -> (step : HasName a l)
                  -> HasName a (Alt l r)

  StepRight : (prf  : Not (HasName a l))
           -> (step : HasName a r)
                   -> HasName a (Alt l r)

-- [ EOF ]
