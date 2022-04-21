module Data.Schema

import public Control.Delayed

import public Data.Bool
import public Data.List1
import public Data.List

import public Data.Schema.Restricted

%default total

public export
data Valid : Type -> Type where
  IsString : Valid String
  IsChar   : Valid Char
  IsNat    : Valid Nat

public export
data Schema : (name : Type) -> Bool -> Type where
  ||| The empty schema.
  Empty : Schema n False

  ||| A schema with a single component.
  Simple : (name   : n)
        -> (v           : Type)
        -> (restriction : Schema.Restriction type)
        -> (prf         : Valid type)
                       -> Schema n True

  ||| A named schema with sub-schema.
  Complex : (name   : n)
         -> (schema : Schema n a)
                   -> Schema n a

  ||| Sequence two schemas where `that` might be infinite.
  SeqEat : (this :      Schema n True)
        -> (that : Inf (Schema n b))
                 ->     Schema n True

  ||| Sequence two schemas where `that` is not infinite.
  SeqEmpty : (this : Schema n  a)
          -> (that : Schema n       b)
                  -> Schema n (a || b)

  ||| Choice between two schemas.
  Alt : (this : Schema n  a)
     -> (that : Schema n       b)
             -> Schema n (a && b)

showRestriction : Schema.Restriction a -> String
showRestriction RestrictedNot = "not restricted"
showRestriction (Restricted predicate) = "restricted"

export
partial
Show n => Show (Schema n b) where
  show Empty = "{}"

  show (Simple name v restriction IsString)
    = "(\{show name} : String is \{showRestriction restriction})"
  show (Simple name v restriction IsChar)
    = "(\{show name} : Char is \{showRestriction restriction})"
  show (Simple name v restriction IsNat)
    = "(\{show name} : Nat is \{showRestriction restriction})"

  show (Complex name schema)
    = "(\{show name} \{show schema})"

  show (SeqEat this that)
    = "(\{show this} <+> \{show that})"

  show (SeqEmpty this that)
    = "(\{show this} <+> \{show that})"

  show (Alt this that)
    = "(\{show this} <|> \{show that})"

namespace API
  public export
  Schema : Type -> Type
  Schema n = Schema n True

%allow_overloads (<|>)

public export %inline
(<|>) : Schema n  a
     -> Schema n       b
     -> Schema n (a && b)
(<|>) = Alt

public export
opt : (s : Schema n True) -> Schema n False
opt s = s <|> Empty

mutual
  public export
  some : Schema n -> Schema n
  some l = SeqEat l (many l)

  public export
  many : Schema n -> Schema n False
  many l = opt (some l)

public export
select : (xs  : List (Schema n b))
      -> (prf : NonEmpty xs) -- so we can use prettier list notation.
             => Schema n b
select (x :: xs) {prf = IsNonEmpty}
    = foldl build x xs
  where
    build : Schema n b -> Schema n b -> Schema n b
    build acc x = rewrite sym (andSameNeutral b) in (acc <|> x)

public export
concat : (xs  : List (Schema n b))
      -> (prf : NonEmpty xs) -- so we can use prettier list notation.
             => Schema n (b && True)
concat (x :: xs) {prf = IsNonEmpty}
      = concat' (x::xs)

  where
    concat' : (xs : List (Schema n b))
                 ->       Schema n (b && isCons xs)
    concat' []
      = rewrite andFalseFalse b in Empty

    concat' (x :: xs)
      = rewrite andTrueNeutral b in
        rewrite sym (orSameAndRightNeutral b (isCons xs)) in
          SeqEmpty x (concat' xs)


-- [ EOF ]
