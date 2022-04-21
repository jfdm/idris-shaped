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
      -> (validType  : Valid type)
               -> Data (Simple name type restriction validType)

  Branch : (name  : n)
        -> (value : Data               complex)
                 -> Data (Complex name complex)

  Empty  : Data Empty

  -- [ Sequencing ]
  --
  -- Eat and Empty are artefacts from the total schema specification.
  -- It would be better if there is a single `Seq` constructor but alas no.

  SeqEat : {sthis : Schema n True}
        -> {sthat : Schema n b}
        -> (this :      Data         sthis)
        -> (that : Inf (Data               sthat))
                ->      Data (SeqEat sthis sthat)

  SeqEmpty : {sthis : Schema n a}
        -> {sthat : Schema n b}
        -> (this : Data           sthis)
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

export
partial
{i : Schema n a} -> Show n => Show (Data i) where
  show (Leaf name value prf IsString) = "\{show name} = \{show value}"
  show (Leaf name value prf IsChar)   = "\{show name} = \{show value}"
  show (Leaf name value prf IsNat)    = "\{show name} = \{show value}"

  show (Branch name value)
    = "{\{show name} = \{show value}}"
  show Empty = "{}"
  show (SeqEat this that)
    = "\{show this} <+> \{show that}"
  show (SeqEmpty this that)
    = "\{show this} <+> \{show that}"
  show (This this)
    = show this
  show (That that)
    = show that
-- [ EOF ]
