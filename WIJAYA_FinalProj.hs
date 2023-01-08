import Data.Char
import Data.List

-- Type declarations and helper functions

-- Variables
type Vars = String
type FName = String
-- Arithmetic expressions
data AExpr = Var Vars | Const Integer
           | Add AExpr AExpr | Sub AExpr AExpr
           | Mul AExpr AExpr | Div AExpr AExpr
           | Exp AExpr AExpr | Mod AExpr AExpr
           | FCall FName [AExpr]
  deriving Show
-- Boolean expressions
data BExpr = TT | FF          -- the true and false constants
           | And BExpr BExpr | Or BExpr BExpr | Not BExpr -- boolean operations
           | Eq  AExpr AExpr  -- equality of arithmetic expressions
           | Lt  AExpr AExpr  -- true if the first is less than the second
           | Lte AExpr AExpr  -- true if it's less than or equal to
  deriving Show
-- Instructions
data Instr = Assign Vars AExpr            -- assign X to the value of an expression
           | IfThenElse BExpr Instr Instr -- conditional
           | While BExpr Instr            -- looping construct
           | Do [Instr]                   -- a block of several instructions
           | Return AExpr                 -- a return statement
           | Nop                          -- the "do nothing" instruction
  deriving Show

data FunDef = FunDef FName [Vars] [Instr] -- This is a procedure, list of instructions should be executed
  deriving Show
-- Environments
type Env = [(Vars,Integer)]
type Def = [FunDef]

update :: (Vars, Integer) -> Env -> Env
update (x,newval) [] = [(x,newval)]
update (x,newval) ((y,v) : e) | x == y = (x,newval) : e
                            | otherwise = (y,v) : update (x,newval) e

lookUp :: Vars -> Env -> Integer
lookUp x e = case (lookup x e) of (Just v) -> v
                                  Nothing -> error $ "Not found: " ++ x

lookupDef :: FName -> Def -> Maybe FunDef
lookupDef n (fd@(FunDef name vars body) : ds) | n == name = Just fd
                                              | otherwise = lookupDef n ds
lookupDef n _ = Nothing

--Evaluators for arithmetic and boolean expressions

evala :: Def -> Env -> AExpr -> Integer
evala d env (Var x)      = lookUp x env
evala d env (Const v)    = v
evala d env (Add p1 p2)  = evala d env p1 + evala d env p2
evala d env (Sub p1 p2)  = evala d env p1 - evala d env p2
evala d env (Mul p1 p2)  = evala d env p1 * evala d env p2
evala d env (Div p1 p2)  = evala d env p1 `div` evala d env p2
evala d env (Exp p1 p2)  = evala d env p1 ^ evala d env p2
evala d env (Mod p1 p2)  = evala d env p1 `mod` evala d env p2
evala d env (FCall n e)  = case lookupDef n d of
        Nothing -> error ("Function name not found: " ++ n)
        Just (FunDef name vars body) -> lookUp "0" (exec (Do body) d e') -- call by value
                            where e' = zip vars (map (evala d env) e)

evalb :: Def -> Env -> BExpr -> Bool
evalb d _ TT = True
evalb d _ FF = False
evalb d e (And b1 b2) = evalb d e b1 && evalb d e b2
evalb d e (Or  b1 b2) = evalb d e b1 || evalb d e b2
evalb d e (Not b) = not $ evalb d e b
evalb d e (Eq  e1 e2) = evala d e e1 == evala d e e2
evalb d e (Lt e1 e2)  = evala d e e1 <  evala d e e2
evalb d e (Lte e1 e2) = evala d e e1 <= evala d e e2

-- Executing instructions.

exec :: Instr -> Def -> Env -> Env
exec (Assign x v) d e = update (x, evala d e v) e
exec (IfThenElse c i1 i2) d e = if evalb d e c then exec i1 d e else exec i2 d e
exec (While c i) d e = if evalb d e c then exec (While c i) d (exec i d e) else e
exec (Do []) d e = e
exec (Do (i:is)) d e = exec (Do is) d (exec i d e)
exec Nop d e = e
exec (Return ae) d e = ("0", evala d e ae) : e

--Lexical analysis

data UOps = NotOp deriving Show
data BOps = AddOp | SubOp | MulOp | DivOp | ModOp | ExpOp
          | AndOp | OrOp  | EqOp  | LtOp  | LteOp
  deriving Show
data Keywords = IfK | ThenK | ElseK | WhileK | NopK | FDefK String
  deriving Show
data Token = VSym String | CSym Integer | BSym Bool
           | UOp UOps | BOp BOps | AssignOp
           | LPar | RPar | LBra | RBra | LSqr | RSqr| Semi
           | Keyword Keywords
           | PV [Vars]
           | PF FunDef
           | Err String
           | Ret
           | SymAt
           | ArgBlock [AExpr]
           | PA AExpr | PB BExpr | PI Instr | Block [Instr]
  deriving Show

lexer :: String -> [Token]
lexer "" = []
-- boolean operators. putting these first because /\ must be checked before /
lexer ('!':s)      = UOp NotOp : lexer s
lexer ('/':'\\':s) = BOp AndOp : lexer s
lexer ('\\':'/':s) = BOp OrOp  : lexer s
lexer ('=':'=':s)  = BOp EqOp  : lexer s
lexer ('<':'=':s)  = BOp LteOp : lexer s
lexer ('<':s)      = BOp LtOp  : lexer s
-- arithmetic operators
lexer ('+':s) = BOp AddOp : lexer s
lexer ('*':s) = BOp MulOp : lexer s
lexer ('-':s) = BOp SubOp : lexer s
lexer ('/':s) = BOp DivOp : lexer s
lexer ('%':s) = BOp ModOp : lexer s
lexer ('^':s) = BOp ExpOp : lexer s
-- punctuation
lexer ('(':s) = LPar : lexer s
lexer (')':s) = RPar : lexer s
lexer ('[':s) = LSqr : lexer s
lexer (']':s) = RSqr : lexer s
lexer ('{':s) = LBra : lexer s
lexer ('}':s) = RBra : lexer s
lexer (';':s) = Semi : lexer s
lexer ('@':s) = SymAt : lexer s
-- keywords
lexer (':':'=':s)             = AssignOp       : lexer s
lexer s | take 2 s == "if"    = Keyword IfK    : lexer (drop 2 s)
lexer s | take 4 s == "then"  = Keyword ThenK  : lexer (drop 4 s)
lexer s | take 4 s == "else"  = Keyword ElseK  : lexer (drop 4 s)
lexer s | take 5 s == "while" = Keyword WhileK : lexer (drop 5 s)
lexer s | take 3 s == "nop"   = Keyword NopK   : lexer (drop 3 s)
--return
lexer s | take 6 s == "return" = Ret : lexer (drop 6 s)
-- constants and variables
lexer ('T':s) | notFun s = BSym True  : lexer s
lexer ('F':s) | notFun s = BSym False : lexer s
lexer (c:s) | isDigit c = let (ds,rs) = span isDigit s
                          in CSym (read (c:ds)) : lexer rs
lexer (c:s) | isLower c = let (vs,rs) = span isAlphaNum s
                          in VSym (c:vs) : lexer rs
lexer (c:s) | isUpper c = let (vs,rs) = span isAlphaNum s
                          in Keyword (FDefK (c:vs)) : lexer rs
-- other
lexer (c:s) | isSpace c = lexer s
lexer s = error ("Unrecognized token: " ++ s)

notFun :: String -> Bool
notFun (x:xs) = not (isAlphaNum x)
notFun _ = True


-- Question 4. Parsing

parseAExpr :: [Token] -> AExpr
parseAExpr ts = case sr [] ts of
  [PA e] -> e
  s      -> error ("Parse error:" ++ show s)

parseBExpr :: [Token] -> BExpr
parseBExpr ts = case sr [] ts of
  [PB e] -> e
  s      -> error ("Parse error:" ++ show s)

parseInstr :: [Token] -> Instr
parseInstr ts = case sr [] ts of
  [PI i] -> i
  s      -> error ("Parse error:" ++ show s)

parseDef :: [Token] -> FunDef
parseDef ts = case sr [] ts of
  [PF f] -> f
  s      -> error ("Parse error: " ++ show s)

parseSplit :: [Token] -> ([Token], [Token])
parseSplit [] = ([],[])
parseSplit (SymAt:ts) = let (x,SymAt:y) = span isSymAt ts in (x,y)

defSplit :: [Token] -> [FunDef]
defSplit [] = []
defSplit ts = let (x,y) = parseSplit ts in parseDef x : defSplit y

isSymAt :: Token -> Bool
isSymAt SymAt = False
isSymAt _ = True

-- The main parsing function alternates between shifting elements
-- from the input queue to the parse stack, and reducing the top of the stack
sr :: [Token] -> [Token] -> [Token]
--return 
sr (PA p1 : Ret : ts)  q = sr (PI (Return p1) : ts) q
-- variables and constants
sr (VSym x : ts)     q = sr (PA (Var  x) : ts) q
sr (CSym x : ts)     q = sr (PA (Const x) : ts) q
sr (BSym True : ts)  q = sr (PB TT : ts) q
sr (BSym False : ts) q = sr (PB FF : ts) q
-- arithmetic operations
sr (PA p2 : BOp AddOp : PA p1 : ts) q = sr (PA (Add p1 p2) : ts) q
sr (PA p2 : BOp SubOp : PA p1 : ts) q = sr (PA (Sub p1 p2) : ts) q
sr (PA p2 : BOp MulOp : PA p1 : ts) q = sr (PA (Mul p1 p2) : ts) q
sr (PA p2 : BOp DivOp : PA p1 : ts) q = sr (PA (Div p1 p2) : ts) q
sr (PA p2 : BOp ModOp : PA p1 : ts) q = sr (PA (Mod p1 p2) : ts) q
sr (PA p2 : BOp ExpOp : PA p1 : ts) q = sr (PA (Exp p1 p2) : ts) q
-- boolean operations
sr (PB p : UOp NotOp : ts)          q = sr (PB (Not p) : ts) q
sr (PB p2 : BOp AndOp : PB p1 : ts) q = sr (PB (And p1 p2) : ts) q
sr (PB p2 : BOp OrOp  : PB p1 : ts) q = sr (PB (Or  p1 p2) : ts) q
-- comparisons and assignment operation
sr (PA p2 : BOp EqOp : PA p1 : ts) q = sr (PB (Eq p1 p2) : ts) q
sr (PA p2 : BOp LtOp  : PA p1 : ts) q = sr (PB (Lt p1 p2) : ts)  q
sr (PA p2 : BOp LteOp : PA p1 : ts) q = sr (PB (Lte p1 p2) : ts) q
sr (PA p : AssignOp : PA (Var x) : ts) q = sr (PI (Assign x p) : ts) q
-- keywords
sr (PI i0 : PB b : Keyword WhileK : ts) q = sr (PI (While b i0) : ts) q
sr (Keyword NopK : ts)                  q = sr (PI Nop : ts) q
sr (PI i2 : Keyword ElseK : PI i1 : Keyword ThenK : PB b : Keyword IfK :ts) q
                                           = sr (PI (IfThenElse b i1 i2) : ts) q
-- parentheses  
sr (RPar : PA p : LPar : ts)        q = sr (PA p : ts) q
sr (RPar : PB p : LPar : ts)        q = sr (PB p : ts) q
sr (RBra : PI p : LBra : ts)        q = sr (PI p : ts) q
-- parsing blocks for functions
sr (LPar : Keyword (FDefK s) : ts)      q = sr (ArgBlock [] : Keyword (FDefK s) : ts) q
sr (PA e : ArgBlock args : ts)          q = sr (ArgBlock (e:args) : ts) q
sr (RPar : ArgBlock args : Keyword (FDefK s) : ts) q = sr (PA (FCall s (reverse args)) : ts) q
-- parsing the FunDef
sr (LSqr : ts)                                    q = sr (PV [] : LSqr : ts) q
sr (PV p : LSqr : ts)                             (VSym q:qs) = sr (PV (p ++ [q]) : LSqr : ts) qs --specifically to parse function definition (list of variables) (args)
sr (RSqr : PV p : LSqr : ts)                      q = sr (PV p : ts) q
sr (Block i : PV p : Keyword (FDefK s) : LBra : ts)    q = sr (PF (FunDef s p i) : ts) q
sr (PI (Do i) : PV p : Keyword (FDefK s) : ts)         q = sr (PF (FunDef s p i) : ts) q
-- parsing do blocks
sr (RBra : PI i : ts)            q = sr (Block [i] : ts) q
sr (RBra : ts)                   q = sr (Block []  : ts) q
sr (Block is : Semi : PI i : ts) q = sr (Block (i:is) : ts) q
sr (Block is : LBra : ts)        q = sr (PI (Do is) : ts)   q
-- shift and return
sr s (i:q) = sr (i:s) q
sr s []    = s

parser :: [Token] -> [Instr]
parser ts = case sr [] (LBra : ts ++ [RBra]) of
  [PI (Do p)] -> p
  s -> error $ "Parse error: " ++ show s

-- I/O

main :: IO ()
main = do
  putStrLn "Enter a file to load"
  filename <- getLine
  input <- readFile filename
  let lexed = lexer input
  let listOfFunDef = defSplit lexed
  let result = evala listOfFunDef [] (FCall "Main" [])
  print result