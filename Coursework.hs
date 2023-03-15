
--------------------------------------------
--                                        --
--         Coursework 2020/2021           --
--                                        --
--------------------------------------------


------------------------- Auxiliary functions

find :: (Show a,Eq a) => a -> [(a,b)] -> b
find x [] = error ("find: " ++ show x ++ " not found")
find x ((y,z):zs)
  | x == y    = z
  | otherwise = find x zs


merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys


------------------------- Lambda-terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
  deriving Eq


instance Show Term where
  show = f 0
    where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

free :: Term -> [Var]
free (Variable x) = [x]
free (Lambda x n) = free n `minus` [x]
free (Apply  n m) = free n `merge` free m


------------------------- Types

infixr 5 :->

type Atom = String
data Type = At Atom | Type :-> Type
  deriving Eq

instance Show Type where
  show (At a)       = a
  show (At a :-> s) = a ++ " -> " ++ show s
  show    (t :-> s) = "(" ++ show t ++ ") -> " ++ show s


atoms :: [Atom]
atoms = map (:[]) ['a'..'z'] ++ [ a : show i | i <- [1..], a <- ['a'..'z'] ]

t1 :: Type
t1 = At "a" :-> At "b"

t2 :: Type
t2 = (At "c" :-> At "d") :-> At "e"

t3 :: Type
t3 = At "a" :-> At "c" :-> At "c"


------------------------- Assignment 1

occurs :: Atom -> Type -> Bool
occurs n (At x)    = n == x
occurs n (x :-> y) = occurs n x || occurs n y

findAtoms :: Type -> [Atom]
findAtoms (At x)    = [x]
findAtoms (x :-> y) = findAtoms x `merge` findAtoms y


------------------------- Type substitution

type Sub = (Atom,Type)

s1 :: Sub
s1 = ("a", At "e")

s2 :: Sub
s2 = ("e", At "b" :-> At "c")

s3 :: Sub
s3 = ("c", At "a" :-> At "a")


------------------------- Assignment 2

sub :: Sub -> Type -> Type
sub (alpha, tau) (At x)
  | x == alpha   = tau
  | otherwise    = At x
sub s (x :-> y)  = sub s x :-> sub s y

subs :: [Sub] -> Type -> Type
subs n = aux (reverse n)
  where
    aux []     y = y
    aux (x:xs) y = aux xs (sub x y)


------------------------- Unification

type Upair = (Type,Type)
type State = ([Sub],[Upair])

u1 :: Upair
u1 = (t1,At "c")

u2 :: Upair
u2 = (At "a" :-> At "a",At "a" :-> At "c")

u3 :: Upair
u3 = (t1,t2)

u4 :: Upair
u4 = (t2,t3)

st1 :: State
st1 = ([],[u1,u2])


------------------------- Assignment 3

sub_u :: Sub -> [Upair] -> [Upair]
sub_u _ [] = []
sub_u s (x:xs) = aux x : sub_u s xs
  where
    aux :: Upair -> Upair
    aux (sigma, tau) = (sub s sigma, sub s tau)

step :: State -> State
step (s, [])                    = (s, [])
step (s, (At p, At q):us)
  | p == q                      = (s, us)
step (s, (At p, q):us)
  | occurs p q                  = error ("Step: atom " ++ p ++ " occurs in " ++ show q)
  | otherwise                   = ((p, q) : s, sub_u (p, q) us )
step (s, (p, At q):us)
  | occurs q p                  = error ("Step: atom " ++ q ++ " occurs in " ++ show p)
  | otherwise                   = ((q, p) : s, sub_u (q, p) us )
step (s, (a :-> b, c :-> d):us) = (s,[(a, c),(b, d)] ++ us)

unify :: [Upair] -> [Sub]
unify x = aux ([], x)
 where
   aux :: State -> [Sub]
   aux (s, u)
     | null u    = s
     | otherwise = aux (step (s, u))


------------------------- Assignment 4

type Context   = [(Var, Type)]
type Judgement = (Context, Term, Type)

data Derivation =
    Axiom       Judgement
  | Abstraction Judgement Derivation
  | Application Judgement Derivation Derivation

n1 :: Term
n1 = Apply (Lambda "x" (Variable "x"))  (Variable "y")


d1 :: Derivation
d1 = Application ([("y",At "a")], n1 , At "a") (
       Abstraction ([("y",At "a")],Lambda "x" (Variable "x"),At "a" :-> At "a") (
         Axiom ([("x",At "a"),("y",At "a")],Variable "x",At "a")
     ) ) (
       Axiom ([("y",At "a")], Variable "y", At "a")
     )

d2 :: Derivation
d2 = Application ([("y",At "b")],Apply (Lambda "x" (Apply (Variable "x") (Variable "y"))) (Lambda "z" (Variable "z")),At "a") (
       Abstraction ([("y",At "b")],Lambda "x" (Apply (Variable "x") (Variable "y")),At "c") (
         Application ([("x",At "d"),("y",At "b")],Apply (Variable "x") (Variable "y"),At "e") (
           Axiom ([("x",At "d"),("y",At "b")],Variable "x",At "f")
         ) (
           Axiom ([("x",At "d"),("y",At "b")],Variable "y",At "g")
     ) ) ) (
       Abstraction ([("y",At "b")],Lambda "z" (Variable "z"),At "h") (
         Axiom ([("z",At "i"),("y",At "b")],Variable "z",At "j")
     ) )


conclusion :: Derivation -> Judgement
conclusion (Axiom j) = j
conclusion (Abstraction j _) = j
conclusion (Application j _ _) = j


subs_ctx :: [Sub] -> Context -> Context
subs_ctx s []          = []
subs_ctx s ((v, t):xs) = (v, (subs s t)) : subs_ctx s xs

subs_jdg :: [Sub] -> Judgement -> Judgement
subs_jdg s (c, te, ty) = ((subs_ctx s c), te, (subs s ty))

subs_der :: [Sub] -> Derivation -> Derivation
subs_der s (Axiom       j)     = Axiom       (subs_jdg s j)
subs_der s (Abstraction j d)   = Abstraction (subs_jdg s j) (subs_der s d)
subs_der s (Application j d e) = Application (subs_jdg s j) (subs_der s d) (subs_der s e)



------------------------- Typesetting derivations


instance Show Derivation where
  show d = unlines (reverse strs)
    where
      (_,_,_,strs) = showD d

      showC :: Context -> String
      showC [] = []
      showC [(x,t)]    = x ++ ": " ++ show t
      showC ((x,t):cx) = x ++ ": " ++ show t  ++ " , " ++ showC cx

      showJ :: Judgement -> String
      showJ ([],n,t) =              "|- " ++ show n ++ " : " ++ show t
      showJ (cx,n,t) = showC cx ++ " |- " ++ show n ++ " : " ++ show t

      showL :: Int -> Int -> Int -> String
      showL l m r = replicate l ' ' ++ replicate m '-' ++ replicate r ' '

      showD :: Derivation -> (Int,Int,Int,[String])
      showD (Axiom j) = (0,k,0,[s,showL 0 k 0]) where s = showJ j; k = length s
      showD (Abstraction j d)   = addrule (showJ j) (showD d)
      showD (Application j d e) = addrule (showJ j) (sidebyside (showD d) (showD e))

      addrule :: String -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      addrule x (l,m,r,xs)
        | k <= m     = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL  l m r  : xs)
        | k <= l+m+r = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL ll k rr : xs)
        | otherwise  = (0,k,0, x : replicate k '-' : [ replicate (-ll) ' ' ++ y ++ replicate (-rr) ' ' | y <- xs])
        where
          k = length x
          i = div (m - k) 2
          ll = l+i
          rr = r+m-k-i

      extend :: Int -> [String] -> [String]
      extend i strs = strs ++ repeat (replicate i ' ')

      sidebyside :: (Int,Int,Int,[String]) -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      sidebyside (l1,m1,r1,d1) (l2,m2,r2,d2)
        | length d1 > length d2 = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip d1 (extend (l2+m2+r2) d2)])
        | otherwise             = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip (extend (l1+m1+r1) d1) d2])



------------------------- Assignment 5


derive0 :: Term -> Derivation
derive0 x = aux ([(f, At "") | f <- free x], x, At "")
  where
    aux :: Judgement -> Derivation
    aux (c, Variable var, y) = Axiom       (c, Variable var, y)
    aux (c, Lambda var t, y) = Abstraction (c, Lambda var t, y) 
                                           (aux ((var, At "") : [n | n <- c, m <- [(var, At "")], n /= m], t, y))
    aux (c, Apply  m   n, y) = Application (c, Apply  m n, y) 
                                           (aux (c, m, y)) 
                                           (aux (c, n, y))

derive1 :: Term -> Derivation
derive1 x = aux (minus atoms (getAtomsJ temp)) temp
  where
    temp :: Judgement
    temp = ([(a, At b) | (a, b) <- zip (free x) (tail atoms)], x, At (head atoms)) 
    
    aux :: [Atom] -> Judgement -> Derivation
    aux a (c, Variable var, y) = Axiom       (c, Variable var, At (head a))
    aux a (c, Lambda var t, y) = Abstraction (c, Lambda var t, y) (aux (minus a (getAtomsJ temp)) temp)
      where 
        temp :: Judgement
        temp = ((var, At (head a)) : [(n,ns) | (n,ns) <- c, (m,ms) <- [(var, At "")], n /= m], t, At (head (tail a)))
    aux a (c, Apply  m   n, y) = Application (c, Apply  m n, y) 
                                             (aux (minus [y | (y, i) <- zip a [0..], even i] (getAtomsJ temp )) temp) 
                                             (aux (minus [z | (z, j) <- zip a [0..], odd  j] (getAtomsJ temp2)) temp2)
      where
        temp :: Judgement
        temp =  (c, m, At (head a))
        temp2 :: Judgement
        temp2 = (c, n, At (head (tail a)))


getAtomsC :: Context -> [Atom]
getAtomsC []          = []
getAtomsC [(_, x)]    = getAtoms [x]
getAtomsC ((_, x):xs) = getAtoms [x] `merge` getAtomsC xs

getAtomsJ :: Judgement -> [Atom]
getAtomsJ (c, _, t) = getAtomsC c `merge` getAtoms [t]

getAtomsD :: Derivation -> [Atom]
getAtomsD (Axiom j)           = getAtomsJ j 
getAtomsD (Abstraction j d)   = getAtomsJ j `merge` getAtomsD d
getAtomsD (Application j d e) = getAtomsJ j `merge` getAtomsD d `merge` getAtomsD e

getAtoms :: [Type] -> [Atom]
getAtoms = foldr (merge . findAtoms) []


upairs :: Derivation -> [Upair]
upairs (Axiom (c, Variable var, y)) = [(y, find var c)]
upairs (Abstraction (c, Lambda var t, y) d) = (y, getTypeFromContext (Variable var) d :-> getType d) : upairs d
upairs (Application (c, Apply m n, y) d e) = (getType d, getType e :-> y) : upairs d ++ upairs e

getTypeFromContext :: Term -> Derivation -> Type
getTypeFromContext (Variable x) (Axiom (c, _, _)) = find x c 
getTypeFromContext (Variable x) (Abstraction (c, _, _) _) = find x c 
getTypeFromContext (Variable x) (Application (c, _, _) _ _) = find x c 

getType :: Derivation -> Type
getType (Axiom (_, _, y))           = y
getType (Abstraction (_, _, y) _)   = y
getType (Application (_, _, y) _ _) = y

derive :: Term -> Derivation
derive x = subs_der (unify (upairs (derive1 x))) (derive1 x)

