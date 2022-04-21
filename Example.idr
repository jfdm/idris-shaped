module Example

import Data.Schema.Restricted
import Data.Schema
import Data.Schema.Data
import Data.Schema.Path

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

Show Name where
  show Employee   = "Employee"
  show PersonInfo = "PersonInfo"
  show FullName   = "FullName"
  show Firstname  = "Firstname"
  show Lastname   = "Lastname"
  show Address    = "Address"
  show FirstLine  = "FirstLine"
  show City       = "City"
  show Country    = "Country"
  show PostCode   = "PostCode"

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
          (concat [Complex FullName (concat [Simple Firstname String RestrictedNot IsString
                                            ,Simple Lastname  String RestrictedNot IsString
                                            ])
                  ,select [Simple Address String RestrictedNot IsString
                          ,(concat [Simple FirstLine String RestrictedNot           IsString
                                   ,Simple City      String RestrictedNot           IsString
                                   ,Simple Country   String (Restricted IsUpperStr) IsString
                                   ,Simple PostCode  String RestrictedNot           IsString
                                   ])]]))


-- [ Example Data ]

||| One employee
employee0 : Data EmployeeSchema
employee0
  = Branch Employee
      (Branch PersonInfo
        (SeqEmpty (Branch FullName (SeqEmpty (Leaf Firstname "Thor" RestrictedNot IsString)
                                   (SeqEmpty (Leaf Lastname "Odinson" RestrictedNot IsString)
                                             Empty)))
        (SeqEmpty (This (Leaf Address "Asgard" RestrictedNot IsString))
                  Empty)))

||| Another Employee
employee1 : Data EmployeeSchema
employee1
  = Branch Employee
      (Branch PersonInfo
        (SeqEmpty (Branch FullName (SeqEmpty (Leaf Firstname "Loki" RestrictedNot IsString)
                                   (SeqEmpty (Leaf Lastname "Laufison" RestrictedNot IsString)
                                             Empty)))
        (SeqEmpty (That (SeqEmpty (Leaf FirstLine "The Frost Palace" RestrictedNot IsString)
                        (SeqEmpty (Leaf City      "Jotun City"       RestrictedNot IsString)
                        (SeqEmpty (Leaf Country "JH" (Restricted (S (C (YesIUC Refl) (C (YesIUC Refl) E)))) IsString)
                        (SeqEmpty (Leaf PostCode "JH01" (RestrictedNot) IsString)
                                  Empty)))))
                  Empty)))


||| Employee/PersonInfo/*
Query0 : Query EmployeeSchema
Query0
  = Q (StepDown Employee (All PersonInfo))


||| Employee/PersonInfo/FullName
Query1 : Query EmployeeSchema
Query1
  = Q (StepDown Employee (StepDown PersonInfo (ThisChildEmpty (Node FullName))))

|||
Query2 : Query EmployeeSchema
Query2
  = Q (StepDown Employee (StepDown PersonInfo (NextChildEmpty (ThisChildEmpty (GoLeft (Atom Address))))))


-- [ EOF ]
