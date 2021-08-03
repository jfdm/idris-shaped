module Example

import Data.Schema.Restricted
import Data.Schema
import Data.Schema.Data

%default total

-- [ Example Predicates on Data ]
data IsUpperC : Char -> Type where
  YesIUC : (isUpper c = True) -> IsUpperC c

data IsUpperCS : List Char -> Type where
  E : IsUpperCS Nil
  C : IsUpperC c -> IsUpperCS cs -> IsUpperCS (c::cs)

data IsUpperStr : String -> Type where
  S : IsUpperCS (unpack s) -> IsUpperStr s


data Name
  = Employee
  | PersonInfo
  | FullName
  | Firstname
  | Lastname
  | Address
  | FirstLine
  | City
  | Country
  | PostCode

||| An Example Schema to describe Employees.
|||
||| The corresponding XSD Schema would potentially be:
|||
||| ```xsd
||| <xs:element name="employee" type="fullpersoninfo"/>
||| <xs:complexType name="personinfo">
|||   <xs:sequence>
|||     <xs:element name="firstname" type="xs:string"/>
|||     <xs:element name="lastname" type="xs:string"/>
|||   </xs:sequence>
||| </xs:complexType>
||| <xs:complexType name="fullpersoninfo">
|||   <xs:complexContent>
|||     <xs:extension base="personinfo">
|||       <xs:sequence>
|||         <xs:element name="address" type="xs:string"/>
|||         <xs:element name="city" type="xs:string"/>
|||         <xs:element name="country" type="xs:string"/>
|||       </xs:sequence>
|||     </xs:extension>
|||   </xs:complexContent>
||| </xs:complexType>
||| ```
|||
EmployeeSchema : Schema Name
EmployeeSchema
  = Complex Employee
      (Complex PersonInfo
          (concat [Complex FullName (concat [Simple $ MkAtom Firstname String RestrictedNot IsString
                                            ,Simple $ MkAtom Lastname  String RestrictedNot IsString
                                            ])
                  ,select [Simple $ MkAtom Address String RestrictedNot IsString
                          ,(concat [Simple $ MkAtom FirstLine String RestrictedNot           IsString
                                   ,Simple $ MkAtom City      String RestrictedNot           IsString
                                   ,Simple $ MkAtom Country   String (Restricted IsUpperStr) IsString
                                   ,Simple $ MkAtom PostCode  String RestrictedNot           IsString
                                   ])]]))


-- [ Example Data ]

||| One employee
employee0 : Data EmployeeSchema
employee0
  = Branch Employee
      (Branch PersonInfo
        (SeqEmpty (Branch FullName (SeqEmpty (Leaf Firstname "Thor" RestrictedNot)
                                   (SeqEmpty (Leaf Lastname "Odinson" RestrictedNot)
                                             Empty)))
        (SeqEmpty (This (Leaf Address "Asgard" RestrictedNot))
                  Empty)))

||| Another Employee
employee1 : Data EmployeeSchema
employee1
  = Branch Employee
      (Branch PersonInfo
        (SeqEmpty (Branch FullName (SeqEmpty (Leaf Firstname "Loki" RestrictedNot)
                                   (SeqEmpty (Leaf Lastname "Laufison" RestrictedNot)
                                             Empty)))
        (SeqEmpty (That (SeqEmpty (Leaf FirstLine "The Frost Palace" RestrictedNot)
                        (SeqEmpty (Leaf City      "Jotun City"       RestrictedNot)
                        (SeqEmpty (Leaf Country "JH" (Restricted (S (C (YesIUC Refl) (C (YesIUC Refl) E)))))
                        (SeqEmpty (Leaf PostCode "JH01" (RestrictedNot))
                                  Empty)))))
                  Empty)))


-- [ EOF ]
