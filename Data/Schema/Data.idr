||| Shaped data.
module Data.Schema.Data

import Data.Schema.Restricted
import Data.Schema

%default total

public export
data Data : Schema n b -> Type where
 -- [ Shape ]
 --
 -- The core shape of data is that of a Rose Tree: Leaves are concrete values; and branches are nodes.
 -- We differ by loosing the restrictions on node shapes.
 --
  Leaf : (name  : n)
      -> (value : type)
      -> (prf   : Restriction type restriction value)
               -> Data (Simple (MkAtom name type restriction validType))

  Branch : (name  : n)
        -> (value : Data               complex)
                 -> Data (Complex name complex)

  Empty  : Data Empty

  -- [ Sequencing ]
  --
  -- Eat and Empty are artefacts from the total schema specification.
  -- It would be better if there is a single `Seq` constructor but alas no.

  SeqEat : (this :      Data         sthis)
        -> (that : Inf (Data               sthat))
                ->      Data (SeqEat sthis sthat)

  SeqEmpty : (this : Data           sthis)
          -> (that : Data                 sthat)
                  -> Data (SeqEmpty sthis sthat)

  -- [ Choice ]
  --
  -- This and that, may lead to noisy data when `Alt` is nested.
  --
  -- [ Q ] How to address such noisey shaped data?

  This : (this : Data sthis)
              -> Data (Alt sthis sthat)

  That : (that : Data sthat)
              -> Data (Alt sthis sthat)


-- [ EOF ]
