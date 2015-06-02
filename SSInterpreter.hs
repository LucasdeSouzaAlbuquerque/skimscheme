{-

A basic interpreter for a purely functional subset of Scheme named SkimScheme.
Part of this interpreter has been derived from the "Write Yourself a Scheme in
48 Hours - An Introduction to Haskell through Example", by Jonathan Tang. It
does not implement a number of Scheme's constructs. Moreover, it uses a
different approach to implement mutable state within the language.

The name "SkimScheme" refers to the stripped down nature of this interpreter.
According to the New Oxford American Dictionary, "skim" can mean:

(as a verb) ... read (something) quickly or cursorily so as to note only
the important points.

(as a noun) ... an act of reading something quickly or superficially. 

"skimmed/skim milk" is milk from which the cream has been removed. 

The name emphasizes that we do not want to cover the entire standard, small as
it may be. Instead, we want to focus on some of the important aspects, taking a
language implementer's point of view, with the goal of using it as a teaching
tool. Many, many, many aspects of Scheme standards are not covered (it does not
even support recursion!).

Written by Fernando Castor
Started at: August 28th 2012
Last update: December 17th 2012

-}

module Main where
import System.Environment
import Control.Monad
import Data.Map as Map
import LispVal
import SSParser
import SSPrettyPrinter

-----------------------------------------------------------
--                      INTERPRETER                      --
-----------------------------------------------------------
eval :: StateT -> LispVal -> StateTransformer LispVal
eval env val@(String _) = return val
eval env val@(Atom var) = stateLookup env var
eval env val@(Number _) = return val
eval env val@(Bool _) = return val
eval env (List [Atom "quote", val]) = return val
eval env (List (Atom "begin":[v])) = eval env v
eval env (List (Atom "begin": l: ls)) = (eval env l) >>= (\v -> case v of {(error@(Error _)) -> return error; otherwise -> eval env (List (Atom "begin": ls))})
eval env (List (Atom "begin":[])) = return (List [])
eval env lam@(List (Atom "lambda":(List formals):body:[])) = return lam

-- if
eval env (List (Atom "if":check:ifTrue:[])) = (eval env check) >>= (\p -> case p of {(error@(Error _)) -> return error; (Bool True) -> eval env ifTrue; otherwise -> return (Bool False)})
eval env (List (Atom "if":check:ifTrue:ifFalse:[])) = (eval env check) >>= (\p -> case p of {(Bool True) -> eval env ifTrue; (Bool False) -> eval env ifFalse; otherwise -> return (Error "Is it a conditional?")})

-- let
eval env (List (Atom "let":(List vars):expr:[])) = ST (\s -> 
	    let current  = union env s; -- (env + state until the let)
		    extended = prepareState current env vars; -- (env + state until let) + let definitions
		    (ST f) = eval extended expr; 
		    (result, newState) = f s; -- state after let execution
		    afterState = union (difference newState extended) current; -- this removes all variables that were defined on the let procedure
		in (result, afterState)
	  );

-- set!
eval env (List (Atom "set!":(Atom id):expr:[])) = stateLookup env id >>= (\v -> case v of {
  (Error err) -> return $ Error "Variavel não declarada";
  otherwise -> defineVar env id expr})

eval env (List (Atom "set!":_:expr:[])) = return $ Error "Variável não é um identificador"

-- comment
eval env (List (Atom "comment":_:[])) = return (List [])

-- make-closure
eval env clousure@(List (Atom "make-closure":(lam@(List (Atom "lambda":(List formals):body:[]))):[])) = return $ List [(State env) , lam]

-- The following line is slightly more complex because we are addressing the
-- case where define is redefined by the user (whatever is the user's reason
-- for doing so. The problem is that redefining define does not have
-- the same semantics as redefining other functions, since define is not
-- stored as a regular function because of its return type.
eval env (List (Atom "define": args)) = maybe (define env args) (\v -> return v) (Map.lookup "define" env)
eval env (List (Atom func : args)) = mapM (eval env) args >>= apply env func
eval env (Error s)  = return (Error s)
eval env form = return (Error ("Could not eval the special form: " ++ (show form)))

stateLookup :: StateT -> String -> StateTransformer LispVal
stateLookup env var = ST $ 
  (\s -> 
    (maybe (Error "variable does not exist.")
           id (Map.lookup var (union s env)
    ), s))

-- Because of monad complications, define is a separate function that is not
-- included in the state of the program. This saves  us from having to make
-- every predefined function return a StateTransformer, which would also
-- complicate state management. The same principle applies to set!. We are still
-- not talking about local definitions. That's a completely different
-- beast.
define :: StateT -> [LispVal] -> StateTransformer LispVal
define env [(Atom id), val] = defineVar env id val
define env [(List [Atom id]), val] = defineVar env id val

-- recursão
define env ((List (Atom id:formals)):body:[]) = defineVar env id (List [Atom "lambda",(List formals), body]) --define recursion as procedural using lambda

-- define env [(List l), val]
define env args = return (Error "wrong number of arguments")
defineVar env id val = 
  ST (\s -> let (ST f)    = eval env val
                (result, newState) = f s
            in (result, (insert id result newState))
     )

-- The maybe function yields a value of type b if the evaluation of 
-- its third argument yields Nothing. In case it yields Just x, maybe
-- applies its second argument f to x and yields (f x) as its result.
-- maybe :: b -> (a -> b) -> Maybe a -> b
apply :: StateT -> String -> [LispVal] -> StateTransformer LispVal
apply env func args = 
                  case (Map.lookup func env) of
                      Just (Native f)  -> return (f args)
                      otherwise ->
                        (stateLookup env func >>= \res ->
                          case res of
                            List (Atom "lambda" : List formals : body:l) -> lambda env formals body args
                            List [State s , List (Atom "lambda" : List formals : body:l)] -> ST (\sp -> 
                              let (ST fx) = lambda s formals body args;
                                  (res, newState) = fx s;
                              in (res, insert func (List [State newState, List (Atom "lambda" : List formals : body:l) ]) sp )
                              )
                            otherwise -> return (Error $ func ++ " not a function.")
                        )

-- The lambda function is an auxiliary function responsible for
-- applying user-defined functions, instead of native ones. We use a very stupid 
-- kind of dynamic variable (parameter) scoping that does not even support
-- recursion. This has to be fixed in the project.
lambda :: StateT -> [LispVal] -> LispVal -> [LispVal] -> StateTransformer LispVal
lambda env formals body args = 
  let dynEnv = Prelude.foldr (\(Atom f, a) m -> Map.insert f a m) env (zip formals args)
  in  eval dynEnv body

-- auxiliar methods for let
prepareState :: StateT -> StateT -> [LispVal] -> StateT
prepareState env1 env2 ((List ((Atom id):val:[]):[])) = insert id (getValFromST (eval env1 val) env1) env2
prepareState env1 env2 ((List ((Atom id):val:[]):ls)) = prepareState env1 (insert id (getValFromST (eval env1 val) env1) env2) ls

getValFromST :: StateTransformer LispVal -> StateT -> LispVal
getValFromST (ST f) env = fst $ (f env)

-- Initial environment of the programs. Maps identifiers to values. 
-- Initially, maps function names to function values, but there's 
-- nothing stopping it from storing general values (e.g., well-known
-- constants, such as pi). The initial environment includes all the 
-- functions that are available for programmers.
environment :: Map String LispVal
environment = 
            insert "number?"        (Native predNumber)
          $ insert "boolean?"       (Native predBoolean)
          $ insert "list?"          (Native predList)
          $ insert "+"              (Native numericSum)
          $ insert "*"              (Native numericMult)
          $ insert "-"              (Native numericSub)
          $ insert "car"            (Native car)
          $ insert "cdr"            (Native cdr)
          $ insert "cons"           (Native cons)
          $ insert "lt?"            (Native lessThan)
          $ insert "/"              (Native numericDiv)
          $ insert "eqv?"           (Native eqv)
            empty

type StateT = Map String LispVal

-- StateTransformer is a data type that embodies computations
-- that transform the state of the interpreter (add new (String, LispVal)
-- pairs to the state variable). The ST constructor receives a function
-- because a StateTransformer gets the previous state of the interpreter 
-- and, based on that state, performs a computation that might yield a modified
-- state (a modification of the previous one). 
data StateTransformer t = ST (StateT -> (t, StateT))

instance Monad StateTransformer where
  return x = ST (\s -> (x, s))
  (>>=) (ST m) f = ST (\s -> let (v, newS) = m s
                                 (ST resF) = f v
                             in  resF newS
                      )

-----------------------------------------------------------
--          HARDWIRED PREDEFINED LISP FUNCTIONS          --
-----------------------------------------------------------

-- Includes some auxiliary functions. Does not include functions that modify
-- state. These functions, such as define and set!, must run within the
-- StateTransformer monad. 

car :: [LispVal] -> LispVal
car [List (a:as)] = a
car [DottedList (a:as) _] = a
car ls = Error "invalid list."

cdr :: [LispVal] -> LispVal
cdr (List (a:as) : ls) = List as
cdr (DottedList (a:[]) c : ls) = c
cdr (DottedList (a:as) c : ls) = DottedList as c
cdr ls = Error "invalid list."

predNumber :: [LispVal] -> LispVal
predNumber (Number _ : []) = Bool True
predNumber (a:[]) = Bool False
predNumber ls = Error "wrong number of arguments."

predBoolean :: [LispVal] -> LispVal
predBoolean (Bool _ : []) = Bool True
predBoolean (a:[]) = Bool False
predBoolean ls = Error "wrong number of arguments."

predList :: [LispVal] -> LispVal
predList (List _ : []) = Bool True
predList (a:[]) = Bool False
predList ls = Error "wrong number of arguments."

numericSum :: [LispVal] -> LispVal
numericSum [] = Number 0
numericSum l = numericBinOp (+) l

numericMult :: [LispVal] -> LispVal
numericMult [] = Number 1
numericMult l = numericBinOp (*) l

numericSub :: [LispVal] -> LispVal
numericSub [] = Error "wrong number of arguments."
-- The following case handles negative number literals.
numericSub [x] = if onlyNumbers [x]
                 then (\num -> (Number (- num))) (unpackNum x)
                 else Error "not a number."
numericSub l = numericBinOp (-) l

-- We have not implemented division. Also, notice that we have not 
-- addressed floating-point numbers.

numericBinOp :: (Integer -> Integer -> Integer) -> [LispVal] -> LispVal
numericBinOp op args = if onlyNumbers args
                       then Number $ foldl1 op $ Prelude.map unpackNum args
                       else Error "not a number."

onlyNumbers :: [LispVal] -> Bool
onlyNumbers [] = True
onlyNumbers (Number n:ns) = onlyNumbers ns
onlyNumbers ns = False

unpackNum :: LispVal -> Integer
unpackNum (Number n) = n
--- unpackNum a = ... -- Should never happen!!!!

-----------------------------------------------------------
--                 PLAYER MADE FUNCTION                  --
-----------------------------------------------------------
-- cons
cons :: [LispVal] -> LispVal
cons ((l):(List ls):[]) = List (l:ls)
cons ((dn):(DottedList dl da):[]) = DottedList (da:dl) dn -- cons (newHead:(DottedList List Head))
cons _ = Error "wrong type"

-- lessThan
lessThan :: [LispVal] -> LispVal
lessThan ((Number f):(Number l):[]) = Bool (f < l)
lessThan _ = Error "wrong type"

-- numericDiv
numericDiv :: [LispVal] -> LispVal
numericDiv [] = Number 1
numericDiv l = numericBinOp (div) l

-- eqv
getBool :: LispVal -> Bool
getBool (Bool x) = x
getBool _ = False

eqvList :: LispVal -> LispVal -> Bool
eqvList (List []) (List []) = True
eqvList (List []) _ = False
eqvList _ (List []) = False
eqvList (List (x:xs)) (List (y:ys)) = (getBool (eqv (x:y:[]))) && (eqvList (List xs) (List ys))

eqv :: [LispVal] -> LispVal
eqv ((Atom x):(Atom y):[]) = Bool (x == y)
eqv ((List x):(List y):[]) = Bool (eqvList (List x) (List y))
eqv ((DottedList b1 h1):(DottedList b2 h2):[]) = Bool ((getBool (eqv (h1:h2:[]))) && (eqvList (List b1) (List b2)))
eqv ((Number x):(Number y):[]) = Bool (x == y)
eqv ((String x):(String y):[]) = Bool (x == y)
eqv ((Bool x):(Bool y):[]) = Bool (x == y)
eqv _ = Error "types don't match"

-----------------------------------------------------------
--                     main FUNCTION                     --
-----------------------------------------------------------

showResult :: (LispVal, StateT) -> String
showResult (val, defs) = show val ++ "\n" ++ show (toList defs) ++ "\n"

getResult :: StateTransformer LispVal -> (LispVal, StateT)
getResult (ST f) = f empty -- we start with an empty state. 

main :: IO ()
main = do args <- getArgs
          putStr $ showResult $ getResult $ eval environment $ readExpr $ concat $ args 

