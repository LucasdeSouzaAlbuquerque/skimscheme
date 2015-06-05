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

-- Modificação necessária no eval env de begin (genérico para expressões) para poder passar o estado de uma expressão atual para a próxima, após a valoração.
eval env (List (Atom "begin": expr: nextExpr)) = ST $
    (\currSt -> -- pega o estado recebido
        let (ST f) = eval env expr -- define o stateTransformer retornado pela valoração da expressão atual
            (result, newSt) = f currSt -- aplica a ‘função’ sobre o estado recebido atual, gerando um resultado e um novo estado.
        in case result of
            error@(Error _) -> (error, newSt) -- se for erro passa o novo estado com o resultado inválido
            otherwise ->
                let (ST nextF) = eval (union newSt env) (List (Atom "begin" : nextExpr)) -- valoriza a próxima expressão sobre o estado modificado (o gerado após a valoração da próxima expressão unido com o estado ambiente atual)
                    (nextResult, nextSt) = nextF newSt -- aplica o StateTransformer novo ao estado modificado após a valoração da primeira expressão.
                in (nextResult, (union nextSt newSt)) -- retorna o resultado da função aplicada ao novo estado com a união entre os estados gerados pela valoração da expressão e da expressão seguinte
    )

-- em termos gerais - ele substitui a valoração da próxima ‘expressão’ antiga no programa (a recursão de eval) mas ele também pega e passa o estado modificado!

eval env (List (Atom "begin":[])) = return (List [])
eval env lam@(List (Atom "lambda":(List formals):body:[])) = return lam -- acompanhada da keyword lambda há uma função cujas variáveis estão em formals e o corpo da função está em body

-- if
eval env (List (Atom "if":check:ifTrue:[])) = (eval env check) >>= (\p -> case p of {(error@(Error _)) -> return error; (Bool True) -> eval env ifTrue; otherwise -> return (Bool False)})
	-- caso do if sem else, onde se o if for verdadeiro, ifTrue é retornado. Se o if for falso, um resultado inesperado ocorre (#f no nosso caso)
eval env (List (Atom "if":check:ifTrue:ifFalse:[])) = (eval env check) >>= (\p -> case p of {(Bool True) -> eval env ifTrue; (Bool False) -> eval env ifFalse; otherwise -> return (Error "Is it a conditional?")})
	-- caso do if com else, onde se o if for verdadeiro, ifTrue e retornado e, se não, ifFalse é retornado

-- LET - cria um conjunto de variáveis locais
eval env (List (Atom "let":(List letVars):letExpr:[])) = ST (\initialState ->
        let curr  = union env initialState; -- cria um estado Current que é a união entre o ‘environment’ do programa com o estado até o Let;
            letState = makeState curr env letVars; -- chama uma função que estende o estado Current com as ‘definições’ dentro do Let; 
            (ST function) = eval letState letExpr; -- valoriza a expressão dentro do Let sobre o novo estado de sistema;
            (result, postLetState) = function initialState; -- retorna o estado após a execução do bloco (estadoAnterior + regrasDoLet + mudançasNoSistema), caso alguma variável tenha sido modificada, por exemplo, aplicando a função do StateTransformer no estado S;
            finalState = union (difference postLetState letState) curr; -- remove as ‘regras’ definidas pelo Let, para que estas não afetem fora do seu escopo. (o difference entre postLetState e letState retorna as mudanças no sistema);
        in (result, finalState)
      ); 

-- SET - modifica o valor da variável com escopo mais proximo
eval env (List (Atom "set!":(Atom setId):setExpr:[])) = stateLookup env setId >>= (\v -> case v of { 
	-- dá um StateLookup na ID passada dentro do environment: caso ela não tenha sido declarada, aponte erro - caso s, atualize a variável por meio de defineVar com a valoração da expressão.
  (Error err) -> return $ Error "Variavel não declarada";
  otherwise -> defineVar env setId setExpr})

eval env (List (Atom "set!":_:setExpr:[])) = return $ Error "Variável não é um identificador"
-- caso seja passado algo que não seja um identificador, aponta erro

-- comment
eval env (List (Atom "comment":_:[])) = return (List []) -- ignora tudo o que aparece depois da keyword “comment”

-- MAKE-CLOSURE - ao achar um atomo make-closure seguido por uma definição de lambda retorna uma lista com o estado do ambiente até então e a lambda para ser usado no apply.
eval env closure@(List (Atom "make-closure":(lam@(List (Atom "lambda":(List formals):body:[]))):[])) = return $ List [(State env) , lam]

-- The following line is slightly more complex because we are addressing the
-- case where define is redefined by the user (whatever is the user's reason
-- for doing so. The problem is that redefining define does not have
-- the same semantics as redefining other functions, since define is not
-- stored as a regular function because of its return type.
eval env (List (Atom "define": args)) = maybe (define env args) (\v -> return v) (Map.lookup "define" env)
eval env (List (Atom func : args)) = mapM (eval env) args >>= apply env func
eval env (Error s)  = return (Error s)
eval env form = return (Error ("Could not eval the special form: " ++ (show form)))

stateLookup :: StateT -> String -> StateTransformer LispVal -- metodo para procura de variaveis
stateLookup env var = ST $ 
  (\s -> 
    (maybe (Error "variable does not exist.")
           id (Map.lookup var (union env s) -- se encontra, adiciona esta ao ambiente: modificando-se a ordem para priorizar variáveis do estado até então (locais), em vez do ambiente do sistema
    ), s))

-- Because of monad complications, define is a separate function that is not
-- included in the state of the program. This saves  us from having to make
-- every predefined function return a StateTransformer, which would also
-- complicate state management. The same principle applies to set!. We are still
-- not talking about local definitions. That's a completely different
-- beast.
define :: StateT -> [LispVal] -> StateTransformer LispVal -- metodo para definicao de variaveis globais
define env [(Atom id), val] = defineVar env id val
define env [(List [Atom id]), val] = defineVar env id val

-- recursão
define env ((List (Atom id:formals)):body:[]) = defineVar env id (List [Atom "lambda",(List formals), body]) 
-- Definição da função de recursão encapsulando em lambda transformado em uma função de procedure

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

-- Modificação necessária em apply para aceitar Make-Closure
apply :: StateT -> String -> [LispVal] -> StateTransformer LispVal
apply env func args = 
                  case (Map.lookup func env) of 
                      Just (Native f)  -> return (f args) 
					  -- se houver função nativa em func, essa será retornada 
                      otherwise ->
                        (stateLookup env func >>= \res -> 
						-- se não, uma função será procurada
                          case res of 
						  -- executa de acordo com o caso da “função”.
                            List (Atom "lambda" : List formals : body:l) -> lambda env formals body args 
							-- se o caso for no formato de lambda simples, aplica o lambda com o cabeçalho e o corpo da função sob o estado do ambiente.
                            List [State closEnv, lam@(List (Atom "lambda" : List formals : body:l))] -> ST (\currState -> 
							-- caso o formato seja de um estado seguido por uma definição lambda (ou seja, para poder aplicar o make-closure, segue uma ideia similar à definição do Let.
                              let totalEnv = union closEnv env; 
							  -- une-se o environment atual com o environment passado pela valoração de make-closure
                                  (ST currFunc) = lambda totalEnv formals body args; 
				  -- cria-se um StateTransformer aplicando-se lambda com os argumentos e o corpo no environment combinado.
                                  (res, newSt) = currFunc (union totalEnv currState); 
								  -- utiliza-se este StateTransformer para achar o estado após a aplicação do lambda.
                                  newClosSt = intersection newSt closEnv; 
				  -- cria um estado de Closure fazendo a intersecção do estado fornecido pela valoração da cláusura make-closure com o estado após a aplicação do lambda - ou seja, consegue apenas as mudança do sistema!
                                  (ST nextFunc) = eval newClosSt (List [Atom "define", Atom func, List [Atom "make-closure", lam]]); 
				  -- cria um novo StateTransformer valorando a definição da função utilizada na cláusula make-closure sobre o estado criado acima de mudança do sistema - ou seja, um eventual segundo uso.
                                  (nextRes, nextClosSt) = nextFunc $ union newSt $ union env currState; 
				  -- utiliza-se esta StateTransformer sobre a união do estado atual (após a aplicação do lambda) com o ambiente atual com o estado atual (ou seja, todo o estado antes, durante e após o closure)
                                  global = union ( difference nextClosSt (difference closEnv env)) env; 
				  -- retira-se o que à partir de agora será o global pegando-se a união da (diferença entre os estados de ambiente passados com a diferença sobre o próximo estado de closure) com o ambiente atual
                              in (res , global) 
							  -- ou seja, este apply basicamente pega e - dentro da função - consegue criar um estado no qual uma variável local pode ser tratada como global pelas funções que a chamem. Ou seja, o GLOBAL será composto das variáveis MODIFICADAS no bloco de make-closure (as não modificadas são eliminadas na diferença) MAIS o ambiente atual.
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

--makeState - função recursiva que insere um conjunto de regras em um estado atual;
makeState :: StateT -> StateT -> [LispVal] -> StateT
makeState curr env ((List ((Atom id):val:[]):[])) = insert id (getVal (eval curr val) curr) env --insire no state de environment uma variável e o valor correspondido à expressão da regra atribuida;
makeState curr env ((List ((Atom id):val:[]):ls)) = makeState curr (insert id (getVal (eval curr val) curr) env) ls --idem, mas com chamada recursiva caso exista mais de uma regra;

getVal :: StateTransformer LispVal -> StateT -> LispVal
getVal (ST func) environment = fst (func environment) --pega o primeiro valor da tupla da função do StateTransformer aplicada ao environment passado como parâmetro;

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
			-- a partir daqui são funçoes feitas pelo grupo, que precisaram ser adicionadas aqui para que pudessem ser utilizadas em compilação
          $ insert "cons"           (Native cons)
          $ insert "lt?"            (Native lessThan)
          $ insert "/"              (Native numericDiv)
          $ insert "eqv?"           (Native eqv)
          $ insert "conc"           (Native concatenate) -- auxiliar para quicksort
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

car :: [LispVal] -> LispVal -- metodo que retorna a cabeça de uma lista. equivale ao head em Haskell
car [List (a:as)] = a
car [DottedList (a:as) _] = a
car ls = Error "invalid list."

cdr :: [LispVal] -> LispVal -- metodo que retorna o resto de uma lista, ou seja, sua cauda. equivale ao tail em Haskell
cdr (List (a:as) : ls) = List as
cdr (DottedList (a:[]) c : ls) = c
cdr (DottedList (a:as) c : ls) = DottedList as c
cdr ls = Error "invalid list."

predNumber :: [LispVal] -> LispVal -- checagem sobre o tipo do LispVal. Se este não for um numero, um erro é gerado	
predNumber (Number _ : []) = Bool True
predNumber (a:[]) = Bool False
predNumber ls = Error "wrong number of arguments."

predBoolean :: [LispVal] -> LispVal -- checagem sobre o tipo do LispVal. Se este não for um booleano, um erro é gerado
predBoolean (Bool _ : []) = Bool True
predBoolean (a:[]) = Bool False
predBoolean ls = Error "wrong number of arguments."

predList :: [LispVal] -> LispVal -- checagem sobre o tipo do LispVal. Se este não for uma lista, um erro é gerado
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

numericBinOp :: (Integer -> Integer -> Integer) -> [LispVal] -> LispVal  -- aplicacao de uma funcao sobre todos os elementos de uma lista numerica, para o retorno de apenas 1 elemento numerico.
numericBinOp op args = if onlyNumbers args
                       then Number $ foldl1 op $ Prelude.map unpackNum args  -- utiliza foldl1, variacao do foldl, que é semelhante ao foldr
                       else Error "not a number."

onlyNumbers :: [LispVal] -> Bool -- checagem sobre os tipos dos elementos de uma lista
onlyNumbers [] = True
onlyNumbers (Number n:ns) = onlyNumbers ns
onlyNumbers ns = False

unpackNum :: LispVal -> Integer  -- desencapsulamento de inteiros
unpackNum (Number n) = n
--- unpackNum a = ... -- Should never happen!!!!

-----------------------------------------------------------
--                 PLAYER MADE FUNCTION                  --
-----------------------------------------------------------
-- cons 
cons :: [LispVal] -> LispVal -- metodo de concatenacao entre elemento e lista, equivale ao “:” no Haskell
cons ((l):(List ls):[]) = List (l:ls)
cons ((dn):(DottedList dl da):[]) = DottedList (da:dl) dn -- cons (newHead:(DottedList List Head))
cons _ = Error "wrong type"

-- lessThan
lessThan :: [LispVal] -> LispVal -- checa se o 1º numero recebido é menor que o 2º numero.
lessThan ((Number f):(Number l):[]) = Bool (f < l)
lessThan _ = Error "wrong type"

-- numericDiv
numericDiv :: [LispVal] -> LispVal -- metodo para divisão de numeros inteiros
numericDiv [] = Number 1 -- se a lista de LispVal estiver vazia, o numero 1 sera retornado
numericDiv l = numericBinOp (div) l -- se nao, a divisao sera aplicada de acordo com as regras do numericBinOp, que tambem faz as operações de soma, subtracao e multiplicacao

-- eqv
getBool :: LispVal -> Bool -- metodo auxiliar para desencapsulamento de um LispVal que é um Booleano
getBool (Bool x) = x
getBool _ = False

eqvList :: LispVal -> LispVal -> Bool -- metodo auxiliar para o eqv?, para a checagem de igualdade entre listas
eqvList (List []) (List []) = True
eqvList (List []) _ = False
eqvList _ (List []) = False
eqvList (List (x:xs)) (List (y:ys)) = (getBool (eqv (x:y:[]))) && (eqvList (List xs) (List ys))

eqv :: [LispVal] -> LispVal -- metodo que retorna true apenas se os tipos e valores de 2 elementos forem iguais
eqv ((Atom x):(Atom y):[]) = Bool (x == y)
eqv ((List x):(List y):[]) = Bool (eqvList (List x) (List y))
eqv ((DottedList b1 h1):(DottedList b2 h2):[]) = Bool ((getBool (eqv (h1:h2:[]))) && (eqvList (List b1) (List b2)))
eqv ((Number x):(Number y):[]) = Bool (x == y)
eqv ((String x):(String y):[]) = Bool (x == y)
eqv ((Bool x):(Bool y):[]) = Bool (x == y)
eqv _ = Error "types don't match" -- se os tipos forem diferentes, um erro é gerado

concatenate :: [LispVal] -> LispVal -- metodo auxiliar para o quicksort, equivalente ao “++” em Haskell
concatenate ((List x):(List y):[]) = List (x ++ y)
concatenate ((DottedList x h1):(DottedList y h2):[]) = DottedList (x ++ [h2] ++ y) h1
concatenate _ = Error "types don't match"

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

