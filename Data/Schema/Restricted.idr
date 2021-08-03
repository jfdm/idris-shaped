||| A way to capture optional restrictions on values in both the Schema and the Values themselves.
module Data.Schema.Restricted

%default total

namespace Schema

  public export
  data Restriction : (type : Type) -> Type where
    RestrictedNot : Restriction type
    Restricted : (predicate : type -> Type) -> Restriction type

namespace Data

  public export
  data Restriction : (type : Type)
                  -> (mres  : Schema.Restriction type)
                  -> (value : type)
                           -> Type
    where
      RestrictedNot : Restriction type RestrictedNot value

      Restricted : (prf : predicate value)
                       -> Restriction type (Restricted predicate) value

-- [ EOF ]
