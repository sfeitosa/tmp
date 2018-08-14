{-# LANGUAGE TypeOperators #-}

data Expr f = In (f (Expr f))

-- Variables
data Var e = Var String
type VarExpr = Expr Var


-- Field Access
data Field e = Field e String
type FieldExpr = Expr Field

-- Combining 
data (f :+: g) e = Inl (f e) | Inr (g e)

-- Examples
varExample :: Expr Var
varExample = In (Var "x")

fieldExample :: Expr (Var :+: Field)
fieldExample = In (Inr (Field (In (Inl (Var "x"))) "y"))

instance Functor Var where
  fmap f (Var x) = Var x

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
  evalAlgebra (Var x) = In (Var x)

-- Here we need the 'fields' function
--instance Eval Field where
--  evalAlgebra (Field e x) = ?????

--instance (Eval f, Eval g) => Eval (f :+: g) where
--  evalAlgebra (Inl x) = evalAlgebra x
--  evalAlgebra (Inr y) = evalAlgebra y

eval :: Eval f => Expr f -> Expr f
eval expr = foldExpr evalAlgebra expr

