module common where

infix 7 _⇒_
data Ty : Set where
  bool : Ty
  _⇒_ : Ty → Ty → Ty


