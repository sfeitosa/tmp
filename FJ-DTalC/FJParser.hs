-- Haskell parser for Featherweight Java
-- Author: Samuel da Silva Feitosa
-- Date: 01/2018
---------------------------------------------
module FJParser where
import Data.Map

-- Featherweight Java syntactic constructors
--------------------------------------------
-- class C extends C { C_ f_; K M_ }
data Class = Class String String [(Type,String)] Constr [Method]
           deriving (Eq)

-- C(C_ f_) { super(f_); this.f_.f_; }
data Constr = Constr String [(Type,String)] [String] [(String,String)]
            deriving (Eq)

-- C m(C_ x_) { return e; }
--data Method = Method Type String [(Type,String)] Expr
data Method = Method Type String [(Type,String)] 
            deriving (Eq)

--data Expr = Var String                               -- Variable
--          | FieldAccess Expr String                  -- Field Access
--          | MethodInvk Expr String [Expr]            -- Method Invocation
--          | CreateObject String [Expr]               -- Object Instantiation
--          | Cast String Expr                         -- Cast
--          deriving (Eq)

-- DTalC format
data Expr f = In (f (Expr f))

-- Featherweight Java nominal typing
------------------------------------
data Type = TypeClass String
          deriving (Eq)

-- Featherweight Java auxiliary definitions
-------------------------------------------
type Env = Map String Type
type CT = Map String Class

-- Auxiliary definitions to Type-Checking
-----------------------------------------
--data TypeError = VariableNotFound String
--               | FieldNotFound String
--               | ClassNotFound String
--               | MethodNotFound String String
--               | WrongCast String Expr
--               | ParamsTypeMismatch [(Expr,Type)]
--               | UnknownError Expr
--               deriving (Show,Eq)
    
    
-- Function: throwError
-- Objective: Launching a type error.
-- Params: Expected type, Found type, Expression presenting the error.
-- Returns: A type error structure.
----------------------------------------------------------------------
--throwError :: TypeError -> Either TypeError Type 
--throwError e = Left e

showAttrs :: [(Type,String)] -> String
showAttrs [] = ""
showAttrs ((t,s):hs) = show t ++ " " ++ s ++ ";\n  " ++ showAttrs hs

showFormalParams :: [(Type,String)] -> String
showFormalParams [] = ""
showFormalParams [(t,s)] = show t ++ " " ++ s
showFormalParams ((t,s):hs) = show t ++ " " ++ s ++ ", " ++ showFormalParams hs

showAttrAssign :: [(String,String)] -> String
showAttrAssign [] = ""
showAttrAssign [(f,s)] = "    this." ++ f ++ " = " ++ s ++ ";"
showAttrAssign ((f,s):hs) = "    this." ++ f ++ " = " ++ s ++ ";\n" ++ showAttrAssign hs

showParams :: [String] -> String
showParams [] = ""
showParams [s] = s
showParams (h:hs) = h ++ "," ++ showParams hs

showMethods :: [Method] -> String
showMethods [] = ""
showMethods [m] = show m
showMethods (h:hs) = show h ++ "\n  " ++ showMethods hs

--showExprs :: [Expr] -> String
--showExprs [] = ""
--showExprs [e] = show e
--showExprs (h:hs) = show h ++ "," ++ showExprs hs

-------------------
instance Show Class where
  show (Class c b at cn m) = "class " ++ c ++ " extends " ++ b ++ " {\n  " ++ showAttrs at ++ show cn ++ "\n  " ++ showMethods m ++ "\n}"

instance Show Constr where
  show (Constr c fp at ths) = c ++ "(" ++ showFormalParams fp ++ ") {\n    super(" ++ showParams at ++ ");\n" ++ showAttrAssign ths ++ "\n  }"

instance Show Method where
  --show (Method r m fp e) = show r ++ " " ++ m ++ "(" ++ showFormalParams fp ++ ") {\n    return " ++ show e ++ ";\n  }"
  show (Method r m fp) = show r ++ " " ++ m ++ "(" ++ showFormalParams fp ++ ") {\n    return <<EXPR>>" ++ ";\n  }"

instance Show Type where
  show (TypeClass c) = c

--instance Show Expr where
--  show (Var v) = v
--  show (FieldAccess e f) = show e ++ "." ++ f
--  show (MethodInvk e m p) = show e ++ "." ++ m ++ "(" ++ showExprs p ++ ")"
--  show (CreateObject c p) = "new " ++ c ++ "(" ++ showExprs p ++ ")"
--  show (Cast c e) = "((" ++ c ++ ") " ++ show e ++ ")"
