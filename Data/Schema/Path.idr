||| A way to define /Paths/ through data based on their Schema's.
|||
|||Inspired by XPath and an earlier attempt to build it in idris-xml.
|||
module Data.Schema.Path

import Decidable.Equality

import Data.Maybe

import Data.Schema.Restricted
import Data.Schema
import Data.Schema.Data

public export
data Path : (n : Type) -> (xsd_in : Schema n a) -> (xsd_out : Schema n b) -> Type where
  -- [ Nodes ]
  --
  -- Nodes can be:
  --
  -- + anything;
  -- + a leaf that contains a raw value;
  -- + a node that contains shaped data;
  --

  All : {child : Schema n b}
     -> (parent : n)
               -> Path n (Complex parent child)
                         child


  Atom : (name : n)
              -> Path n (Simple name type restriction vtype)
                        (Simple name type restriction vtype)

  Node : (name : n)
              -> Path n (Complex name complex)
                        (Complex name complex)
  -- [ Paths ]
  --
  -- A path tells us how to go down from a root in the data to a prescribed node.
  --

  ||| Step down into the complex structure.
  |||
  StepDown : (parent : n)
          -> (step   : Path n                 child  res)
                    -> Path n (Complex parent child) res

  ||| Select this child.
  ThisChildEat : (step : Path n this               res)
                      -> Path n (SeqEat this that) res

  ||| Select the next child.
  NextChildEat : (step : Path n that               res)
                      -> Path n (SeqEat this that) res

  ||| Select this child.
  ThisChildEmpty : (step : Path n this                 res)
                        -> Path n (SeqEmpty this that) res

  ||| Select the next child.
  NextChildEmpty : (step : Path n that                 res)
                        -> Path n (SeqEmpty this that) res

  ||| Go left in a choice
  |||
  GoLeft : (step : Path n      left        res)
                -> Path n (Alt left right) res

  ||| Go right in a choice
  |||
  GoRight : (step : Path n           right  res)
                 -> Path n (Alt left right) res

export
Show n => Show (Path n i o) where
  show (All parent) = "\{show parent}/*"
  show (Atom name) = show name
  show (Node name) = show name
  show (StepDown parent step)
    = "\{show parent}/\{show step}"

  show (ThisChildEat step)
    = show step
  show (NextChildEat step)   = show step
  show (ThisChildEmpty step) = show step
  show (NextChildEmpty step) = show step
  show (GoLeft step) = show step
  show (GoRight step) = show step

public export
data Query : (xsd : Schema n b) -> Type where
  Q : {xsd_out : Schema n a} -> Path n xsd_in xsd_out  -> Query xsd_in

export
{i : Schema n b}
-> Show n =>
Show (Query i) where
  show (Q p) = show p

runQuery : Path n i o
        -> Data   i
        -> Maybe (Data     o)
runQuery (All parent) (Branch parent value)
 = Just value

runQuery (Atom name) (Leaf name value prf prfV)
  = Just (Leaf name value prf prfV)

runQuery (Node name) (Branch name value)
  = Just (Branch name value)

runQuery (StepDown parent step) (Branch parent value)
  = runQuery step value

runQuery (ThisChildEat step) (SeqEat this that)
  = runQuery step this

runQuery (NextChildEat step) (SeqEat this that)
  = runQuery step that

runQuery (ThisChildEmpty step) d with (d)
  runQuery (ThisChildEmpty step) d | (SeqEmpty this that)
    = runQuery step this

runQuery (NextChildEmpty step) d with (d)
  runQuery (NextChildEmpty step) d | (SeqEmpty this that)
    = runQuery step that

runQuery (GoLeft step) d with (d)
  runQuery (GoLeft step) d | (This this) = runQuery step this
  runQuery (GoLeft step) d | (That that) = Nothing

runQuery (GoRight step) d with (d)
  runQuery (GoRight step) d | (This this) = Nothing
  runQuery (GoRight step) d | (That that) = runQuery step that

public export
data Result : (xsd : Schema n b) -> Type where
  R : {i : Schema n a}
   -> {o : Schema n b}
   -> (value : Data o)
            -> Result i

export
query : {i : Schema n a} -> Query i -> Data i -> Maybe (Result i)
query (Q x) y = case runQuery x y of
                  Nothing => Nothing
                  Just res => Just (R res)

-- [ EOF ]
