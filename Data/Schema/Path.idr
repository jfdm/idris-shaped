||| A way to define /Paths/ through data based on their Schema's.
|||
|||Inspired by XPath and an earlier attempt to build it in idris-xml.
|||
module Data.Schema.Path

import Decidable.Equality

import Data.Maybe

import Data.Schema.Restricted
import Data.Schema

public export
data PathKind
  = NODE  -- A leaf or a node
  | PATH  -- Step through Data

public export
data Path : (n : Type) -> (xsd : Schema n b) -> (k : PathKind) -> Type where
  -- [ Nodes ]
  --
  -- Nodes can be:
  --
  -- + anything;
  -- + a leaf that contains a raw value;
  -- + a node that contains shaped data;
  --

  All : Path n schema NODE

  Atom : (name : n)
              -> Path n (Simple (MkAtom name type restriction vtype)) NODE

  Node : (name : n)
              -> Path n (Complex name complex) NODE

  -- [ Paths ]
  --
  -- A path tells us how to go down from a root in the data to a prescribed node.
  --

  ||| Step down into the complex structure.
  |||
  StepDown : (parent : n)
          -> (step   : Path n                 child     c)
                    -> Path n (Complex parent child) PATH

  ||| Select this child.
  ThisChildEat : (step : Path n this               ty)
                      -> Path n (SeqEat this that) PATH

  ||| Select the next child.
  NextChildEat : (step : Path n that               ty)
                      -> Path n (SeqEat this that) PATH

  ||| Select this child.
  ThisChildEmpty : (step : Path n this                 ty)
                        -> Path n (SeqEmpty this that) PATH

  ||| Select the next child.
  NextChildEmpty : (step : Path n that                 ty)
                        -> Path n (SeqEmpty this that) PATH

  ||| Go left in a choice
  |||
  GoLeft : (step : Path n      left        ty)
                -> Path n (Alt left right) PATH

  ||| Go right in a choice
  |||
  GoRight : (step : Path n           right  ty)
                 -> Path n (Alt left right) PATH

public export
data Query : (xsd : Schema n b) -> Type where
  Q : Path n xsd type -> Query xsd

namespace Raw
  public export
  data Path : (name : Type) -> Type where
    All    : Path n
    Select : n -> Path n
    Step   : n -> Path n -> Path n


  export
  fromPath : DecEq n
           => (path : Path n)
           -> (xsd  : Schema n b)
                   -> Maybe (Query xsd)
  fromPath All xsd = Just (Q All)
  fromPath (Select x) Empty = Nothing
  fromPath (Select x) (Simple (MkAtom y v restriction prf)) with (decEq x y)
    fromPath (Select x) (Simple (MkAtom x v restriction prf)) | (Yes Refl)
      = Just (Q (Atom x))
    fromPath (Select x) (Simple (MkAtom y v restriction prf)) | (No contra)
      = Nothing
  fromPath (Select x) (Complex name schema) with (decEq x name)
    fromPath (Select x) (Complex x schema) | (Yes Refl)
      = Just (Q (Node x))
    fromPath (Select x) (Complex name schema) | (No contra)
      = Nothing
  fromPath (Select x) (SeqEat this that)   = Nothing
  fromPath (Select x) (SeqEmpty this that) = Nothing
  fromPath (Select x) (Alt this that)      = Nothing

  fromPath (Step x y) Empty = Nothing
  fromPath (Step x y) (Simple z) = Nothing
  fromPath (Step x y) (Complex name schema) with (decEq x name)
    fromPath (Step x y) (Complex x schema) | (Yes Refl)
      = do Q r <- fromPath y schema
           pure (Q (StepDown x r))
    fromPath (Step x y) (Complex name schema) | (No contra)
      = Nothing

  fromPath (Step x y) (SeqEat this that)
      = ?argh


  fromPath (Step x y) (SeqEmpty this that)
    = case fromPath (Step x y) this of
        Just (Q p) => pure (Q (ThisChildEmpty p))
        Nothing =>
          do Q p <- fromPath (Step x y) that
             pure (Q (NextChildEmpty p))

  fromPath (Step x y) (Alt this that)
    = case fromPath (Step x y) this of
        Just (Q p) => pure (Q (GoLeft p))
        Nothing => do Q p <- fromPath (Step x y) that
                      pure (Q (GoRight p))



--
--public
--data
--
--public export
--run : Data schema
--   -> Query schema
--   ->
