{----------------------------------------------------
	NFAstream.hs -- John Benjamin jcb638@mail.missouri.edu
	This program lets you build an e-NFA from a regular expression and match
	characters of any language from a stream
	against the regular expression -}

module NFAStream where
import Data.List (nub)
import Control.Monad.State
infixr :|

--
--Data types
--

--basic Bit representation for streaming bits
data Bit = Zero | One deriving (Eq, Ord)

instance Show Bit where
	show Zero = "0"
	show One = "1"

--Data type for Regular Expression
data RegExp a = Sym a | Bar (RegExp a) (RegExp a) | Star (RegExp a) | (RegExp a) :| (RegExp a)

instance Show a => Show (RegExp a) where
	show (Sym x) = show x 
	show (Star x) = "*(" ++ show x ++ ")"
	show (Bar x y) = "(" ++ show x ++ "|" ++ show y ++ ")"
	show (x :| y) = show x ++ show y

--
--Primitives for State machine implementation
--
type St = Integer --States for NFA
type Sts = [St]
--Transition data type, essentially an edge on the state transition graph.
--A transition can hold a value or be an Epsilon transition
data Transition a = Value a St St | Eps St St deriving (Show)

type Ms a = (Enfa a, Sts, Bool)

--State representation for monadic stream input
type M a = State (Ms a)

--Data structure for epsilon NFA. The polymorphic type a represents a symbol in an alphabet
data Enfa a = Enfa {
	states :: Sts,
	sig :: [Transition a],
	start :: St,
	final :: St } 
	deriving (Show)

{-shiftstate from one stream input
--basic use
--1) build nfa using let myNFA = r2n (regular expression)
--2) shiftstate myNFA [0] (character)
-}

--monadic stream
--runState (stream 'a' >> 'stream 'b) (r2s (Sym 'a' :| Sym 'b))
stream :: Eq a => a -> (M a) (Bool)

stream x = do
	(n, s, b) <- get
	let s' = shiftstate n s x
	let b' = elem (final n) s'
	let b'' = b || b'
	put (n, s', b'')
	return (b'')

--helper function to make Ms from a regexp
r2s :: RegExp a -> Ms a
r2s r = ( (r2n r), [0], False )

--core logic of state shifting matching
shiftstate :: Eq a => Enfa a -> Sts -> a -> Sts
shiftstate n s x 
	| s == [(start n)] =
		let
			sigma = (sig n)
			e = eclose s sigma
			v = valmatch x e sigma
			e' = eclose v sigma
		in
			(eclose [(start n)] sigma) ++ e'
	| otherwise =
		let
			sigma = (sig n)
			v = (valmatch x s sigma)
			e = eclose v sigma
		in
			(eclose [(start n)] sigma) ++ e

{-Transition shift supporting functions -}
		
accept :: Sts -> St -> Bool
accept s i = elem i s

--epsilon closure, return list of states following all possible epsilon transitions, list including initial state
eclose :: Sts -> [Transition a] -> Sts
eclose [] _ = []
eclose s t =
	nub (concat [ s, (eclose ( concatMap (\x -> epsconnected x t) s) t) ] )

--follow all epsilon transitions from a single node
epsconnected :: St -> [Transition a] -> Sts
epsconnected s t =
	map (tend) (filter (\x -> epsstart x == s ) t)
	
--return list following all possible transitions across a particular value from some state, list not including initial state
valmatch :: Eq a => a -> Sts -> [Transition a] -> Sts
valmatch n s t =
	concatMap (\x -> valconnected n x t) s

--follow all value transitions from a single node
valconnected :: Eq a => a -> St -> [Transition a] -> Sts
valconnected n s t =
	map (tend) (filter (\x -> valstart x n == s ) t)

tstart :: Transition a -> St
tstart (Value _ x _) = x 
tstart (Eps x _) = x

tend :: Transition a -> St
tend (Value _ _ y) = y
tend (Eps _ y) = y

epsstart :: Transition a -> St
epsstart (Value _ _ _) = -1
epsstart (Eps x _ ) = x

valstart :: Eq a => Transition a -> a -> St
valstart (Value n x _) m 
	| n == m = x
	| otherwise = -1
valstart (Eps _ _) _ = -1



--RegExp To eNFA
--basic use: let myNFA = r2n (regular expression)
--r2n builds NFA using retn function from a skeleton machine with one default starting state 0
r2n :: RegExp a -> Enfa a
r2n r =
	let
		(s, n) = retn r (Enfa {states=[0],sig=[],start=0,final=0}) 0
	in
		n

--Function for generating state graph from Regular Expression components using Thompson's NFA construction
retn :: RegExp a -> Enfa a -> St -> (St, Enfa a)

retn (Sym x) n s =
	let
		newstate = (s+1)
	in
		( (newstate), Enfa {
			states = (states n) ++ [(newstate)],
			sig = (sig n) ++ [(Value x (s) (newstate)) ] ,
			start = start n,
			final = newstate
			} )

retn (x :| y) n s =
	let
		(xstate, xenfa) = retn x n s
	in
		retn y xenfa xstate

retn (Star x) n s =
	let
		startstate = (s+1)
		(xstate, xenfa) = retn x n startstate
		endstate = xstate+1
	in
		( endstate, Enfa {
			states = (states xenfa) ++ [(startstate),(endstate)],
			sig = (sig xenfa) ++ [ (Eps s startstate), (Eps xstate startstate), (Eps xstate endstate), (Eps s endstate)],
			start = start n,
			final = endstate
			} )

retn (Bar x y) n s =
	let
		(xstate, xenfa) = retn x n (s+1)
		(ystate, yenfa) = retn y xenfa (xstate+1)
		endstate = (ystate+1)
	in
		( (endstate), Enfa {
			states = (states yenfa) ++ [(s+1),(xstate+1),endstate],
			sig = concat [ (sig yenfa), [ (Eps (s) (s+1)), (Eps (s) (xstate+1)), (Eps (xstate) (endstate)), (Eps (ystate) (endstate)) ] ],
			start = start n,
			final = endstate
			} )
