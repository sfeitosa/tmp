{-# LANGUAGE TypeOperators #-}
import FJParser
import FJUtils

-- Variables
data Var e = Var String
type VarExpr = Expr Var

-- New 
data New e = New String [e]
type NewExpr = Expr New

-- Field Access
data Field e = Field e String
type FieldExpr = Expr Field

-- Combining 
data (f :+: g) e = Inl (f e) | Inr (g e)

-- Examples
varExample :: Expr Var
varExample = In (Var "x")

newExample :: Expr New
newExample = In (New "Object" [])

newExample2 :: Expr New
newExample2 = In (New "A" [(In (New "Object" [])), (In (New "Object" []))])

fieldExample :: Expr (Var :+: Field)
fieldExample = In (Inr (Field (In (Inl (Var "x"))) "y"))

fieldExample2 :: Expr (New :+: Field)
fieldExample2 = In (Inr (Field (In (Inl (New "A" [In (Inl (New "Object" [])), In (Inl (New "Object" []))]))) "a"))

-- A functor is any data type that defines how fmap applies to it.
-- Data types, lists, functions...
-- Infix <$>
instance Functor Var where
  fmap f (Var x) = Var x

-- We have to use map here...
instance Functor New where
  fmap f (New c pl) = New c (map f pl)

instance Functor Field where
  fmap f (Field e x) = Field (f e) x

instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap f (Inl e1) = Inl (fmap f e1)
  fmap f (Inr e2) = Inr (fmap f e2)

-- Here and below we need CT
foldExpr :: Functor f => (f a -> a) -> Expr f -> a
foldExpr f (In t) = f (fmap (foldExpr f) t)

class Functor f => Eval f where
  evalAlgebra :: f (Expr f) -> Expr f

instance Eval Var where
  evalAlgebra (Var x) = In (Var x) -- Var is a value

instance Eval New where
  evalAlgebra (New c pl) = In (New c pl) -- New is a value

-- Here we need the 'fields' function
instance Eval Field where
  evalAlgebra (Field e f) = In (Field e f) 

-- Here we receive the error!!!!
instance (Eval f, Eval g) => Eval (f :+: g) where
  evalAlgebra (Inl x) = evalAlgebra x
  evalAlgebra (Inr y) = evalAlgebra y

eval :: Eval f => Expr f -> Expr f
eval expr = foldExpr evalAlgebra expr

class Render f where
  render :: Render g => f (Expr g) -> String

pretty :: Render f => Expr f -> String
pretty (In e) = render e

renderP :: Render f => [Expr f] -> String
renderP [] = ""
renderP [(In e)] = render e
renderP (x:xs) = pretty x ++ "," ++ renderP xs

instance Render Var where
  render (Var x) = show x

instance Render New where
  render (New c p) = "new " ++ show c ++ "(" ++ (renderP p) ++ ")"

instance Render Field where
  render (Field e f) = pretty e ++ "." ++ show f

instance (Render f, Render g) => Render (f :+: g) where
  render (Inl x) = render x
  render (Inr y) = render y

