import Prelude hiding (not, and, or, pred, div, mod, gcd, signum)
{-
Implements basic combinator functions, primitive recursive functions,
and from there, the possibility of all computable functions in the
untyped lambda calculus in Haskell.

Convert Church Numerals to Haskell Integers and vice versa with:
    decodeNum(church_numeral)
    makeNum(n)

Church numerals n0-n32 are defined for convenience.

Similarly convert Church Booleans to Haskell Bools with:
    decodeBool(church_boolean)

Evaluate Church operator functions by passing them as an argument
in their proper decode function (apply functions to their arguments with '!'); e.g.
decodeNum (mul ! (suc ! n2) ! (add ! n2 ! n2))      -- == 12
decodeBool (and ! (not ! not ! not ! false) ! true) -- == True

To use, enter the following into a terminal:
    ghci
    :l lambdaCalculus

-- Substitution commands:
%s/^[A-Z]*/\L&/
29,$s/TRUE/\L&/g -- etc. FALSE, NOT, ADD, SUB, MUL, POW
%s/N[1-32]/\L&/g
V + u -- visual select and lowercase

33,$s/#/--/g
33,$s/lambda /Lambda $/g
33,$s/:/ ->/g
-- removing parentheses globally is risky, because any grouping will be lost.
-}

-- This datatype is needed to get around type errors involving
-- lambda expressions where arguments are duplicated; e.g.,
-- \a -> a a
data Expression = Lambda !(Expression -> Expression) | View !Integer

-- lambda function application
Lambda f ! x = f x
View   _ ! _ = error "Error: Something is being applied to View"

{-
--  Helper to view values when decoding individual functions.
    Now we can test that functions work as written.
    For i or other functions that resolve with a single argument we can use:
    view (i ! View 88)  -- == 88
    For ki or other functions that resolve with two arguments:
    view (ki ! View 88 ! View 66) -- == 66
    And so on ...
-}
view (View   i) = i
view (Lambda f) = error "Error: Lambda used with view function"

-- Decode Church Booleans
-- decodeBool (and ! (not ! not ! not ! not ! not ! false) ! true) -- == True
decodeBool :: Expression -> Bool
decodeBool churchBool = case churchBool ! View 1 ! View 0 of
                     View res | res == 0 -> False
                              | res == 1 -> True
                              | otherwise -> error "Error: Nums within View must have been changed!"
                     Lambda _ -> error "Try a Church Boolean next time!"

-- Decode Church Numerals
-- decodeNum (mul ! (suc ! n2) ! (add ! n2 ! n2)) -- == 12
decodeNum :: Expression -> Integer
decodeNum churchNum = case churchNum ! Lambda (\a -> View (1 + view a)) ! View 0 of
                     View res -> res
                     Lambda _ -> error "Try a Church Numeral next time!"

-- id fn
i = Lambda $ \a -> a -- id in Haskell
-- id 2,1 (given 2 args, return arg 1)
k = Lambda $ \a -> Lambda $ \b -> a -- const in Haskell -> const 7 "anything" == 7
-- id 2,2 (given 2 args, return arg 2)
kiPrimitive= Lambda $ \a -> Lambda $ \b -> b
ki = k ! i -- const id in Haskell

-- "lowercase omega" or "self application" combinator
m = Lambda $ \a -> a ! a -- Cannot define in Haskell
--M(M) is the "uppercase omega"; reduces to itself; loops/recurses forever
-- view (m ! m) -- recurses forever

-- Swaps arguments
c = Lambda $ \a -> Lambda $ \b -> Lambda $ \c -> a ! c ! b -- flip in Haskell -> flip const 'a' 'b' == 'b'
-- C(K) is equiv to K(I)

-- Church encodings (booleans)
true = k
false = ki
-- C is extentionally equivalent (same inputs/outputs) with not
not = Lambda $ \a -> a ! false ! true
nottrue = c ! true  -- Extentionally equivalent with NOT true 
notfalse = c ! false  -- Extentionally equalent with NOT false 
-- Study what intentionally equality may amount to--fns are defined differently
and = Lambda $ \a -> Lambda $ \b -> a ! b ! a  -- If a is false, false fn results; if a is true, b fn results
or = Lambda $ \a -> Lambda $ \b -> a ! a ! b  -- If a is true, true fn results; if a is false, b fn results
-- M is extentionally equivalent with OR
-- NOT  C  and OR  M  grant all other booleans of propositional logic
-- Boolean Equality
bequals = Lambda $ \a -> Lambda $ \b -> a ! b ! (Main.not ! b)

-- Church numerals
n0 = Lambda $ \a -> Lambda $ \b -> b -- Note that the a is still needed -> apply a to b zero times
-- N0 = false = KI (equivelent in both senses)
n1 = Lambda $ \a -> Lambda $ \b -> a ! b  -- I* Applies ab to ab
n2 = Lambda $ \a -> Lambda $ \b -> a ! (a ! b) -- Not like I, since it doubles application of a on b
-- ...

-- For a successor fn that takes one of the above numerals as an arg
-- just copy the a position argument (of above, b below) out front to be applied once more.
suc = Lambda $ \a  -> Lambda $ \b -> Lambda $ \c -> b ! (a ! b ! c)

n0Readable = 0
--sucReadable = Lambda $ \a -> a + 1
sucReadable = view ((Lambda $ \a -> View (1 + view a)) ! View 0)

n3 = suc ! n2
-- Function composition combinator; "bluebird combinator"
-- f(g(a))
-- Also pipeline -> apply g to a and pipe the result to f.
-- In Haskell this is built in as the '.' -> odd = not . even
-- Can also use it in prefix notation in Haskell with parens -> (.)
bC = Lambda $ \a -> Lambda $ \b -> Lambda $ \c -> a ! (b ! c)

sucb = Lambda $ \a -> Lambda $ \b -> bC ! b ! (a ! b) -- Alternative successor fn, using B
add = Lambda $ \a -> Lambda $ \b -> a ! suc ! b
-- To mul, apply fn c b times, and do this a times; this is B!
mul = Lambda $ \a -> Lambda $ \b -> Lambda $ \c -> a ! (b ! c)
-- mul just is B (they are alpha equivalent)
-- Interesting to see how B also composes a successor fn

n4 = add ! n2 ! n2
n5 = suc ! (add ! n2  ! n2)
n6 = mul ! n3  ! n2
n7 = suc ! (mul ! n3  ! n2)

-- Thrush
-- Equivalent with CI
-- flip id in Haskell
-- Equivalent with the pow fn!
t = Lambda $ \a -> Lambda $ \b -> b ! a

n8 = t ! n2  ! n3
n9 = t ! n3  ! n2

-- Is/Equals zero fn
isn0 = Lambda $ \a -> a ! (k ! false) ! true

-- Vireo, the smallest data structure in Lambda $ \calculus
-- Equiv with BCT; in Haskell -> flip . flip id
-- The Church pairing fn, which pairs two arguments
v = Lambda $ \a -> Lambda $ \b -> Lambda $ \c -> c ! a ! b

-- Holds on to I and M as arguments to access
vim = v ! i ! m
-- Now access arg1 with K, arg2 with KI
--assert VIM(K) == I
--assert VIM(KI) == M

-- Used on pairs which hold arguments, such as VIM
first = Lambda $ \a -> a ! k
second = Lambda $ \a -> a ! ki

-- Takes a pair, and returns pair of second item,
-- and second item plus 1
phi = Lambda $ \a -> v ! (second ! a) ! (suc ! (second ! a))

-- Applying PHI to (N0, N0), we get (N0, n1)
-- Applying PHI to (N0, N0) 8 times, we get (N7, N8)
-- Notice that the first item is N7, the pred of N8!
pred = Lambda $ \a -> first ! (a ! phi ! (v ! n0 ! n0))

-- Original, more complcated predecessor fn
predequiv = Lambda $ \n -> n !
            (Lambda $ \g -> isn0 ! (g ! n1) ! i ! (bC ! suc ! g)) !
            (k ! n0) ! n0

-- First arg is item to set and second arg is a Church pair
setfirst = Lambda $ \a -> Lambda $ \b -> v ! a ! (second ! b)
setsecond = Lambda $ \a -> Lambda $ \b -> v ! (first ! b) ! a

sub = Lambda $ \a -> Lambda $ \b -> b ! pred ! a

-- Less than or equal
leq = Lambda $ \a -> Lambda $ \b -> isn0 ! (sub ! a ! b)
-- Equals
eq = Lambda $ \a -> Lambda $ \b -> and ! (isn0 ! (sub ! a ! b)) ! (isn0 ! (sub ! b ! a))
-- Greater than
gt = Lambda $ \a -> Lambda $ \b -> not ! (isn0 ! (sub ! a ! b))
-- Less than
lt = Lambda $ \a -> Lambda $ \b -> not ! (isn0 ! (sub ! b ! a))

blackbird = bC ! bC ! bC
gtequiv = blackbird ! not ! leq

n10 = pred ! (suc ! (suc ! n9))
n11 = suc ! (suc ! n9)
n12 = mul ! n3 ! n4
n13 = suc ! (mul ! n3 ! n4)
n14 = suc ! n13
n15 = suc ! n14
n16 = t ! n2  ! n4
n17 = suc ! n16
n18 = suc ! n17
n19 = suc ! n18
n20 = suc ! n19
n21 = suc ! n20
n22 = suc ! n21
n23 = suc ! n22
n24 = suc ! n23
n25 = suc ! n24
n26 = suc ! n25
n27 = t ! n3  ! n3
n28 = suc ! n27
n29 = suc ! n28
n30 = suc ! n29
n31 = suc ! n30
n32 = t ! n2  ! n5
n64 = t ! n2  ! n6

-- Triple data structure
v3 = Lambda $ \a -> Lambda $ \b -> Lambda $ \c -> Lambda $ \d -> d ! a !  b ! c
v3first = Lambda $ \v -> v ! Lambda (\a -> Lambda $ \b -> Lambda $ \c -> a)
v3second = Lambda $ \v -> v ! Lambda (\a -> Lambda $ \b -> Lambda $ \c -> b)
v3third = Lambda $ \v -> v ! Lambda (\a -> Lambda $ \b -> Lambda $ \c -> c)

-- Sub first and second and store as first, keep second, increment third.
-- Can be used with a loop for a div fn that returns the third at the end.
-- Just a prototype.
phidiv = Lambda $ \a -> v3 ! (sub ! (v3first ! a) ! (v3second !a)) ! (v3second ! a) ! (suc ! (v3third ! a))


-- IMPLEMENTING RECURSION.

-- Attempt a FAC fn with explicit recursive call.
-- Rec. limit reached because Python won't short-circuit
-- and so WILL evaluate the last line even when ISNO(a)
-- is false and would just select (n1). Makes sense--
-- Python wouldn't know what our false fn does ahead of
-- such evaluations, as it does know with, say, 'False and 4 / 0'.
facv1 = Lambda $ \a -> isn0 ! a !
            n1 !
            (mul !a ! (facv1 ! (pred ! a)))
-- Above, the fn repeats evaluating the last line when a is N0
-- We can get around this by delaying the evaluation (implementing
-- our own lazy evaluation in place of the eager evaluation).
-- We do this by reimplementing our true and false fns to select
-- and then call as a fn what is selected. This requires that
-- what gets selected be evaluated after being called; which is
-- done by just converting the selections to be zero-argument lambdas.

--Unneeded in haskell:lazytrue = Lambda $ \a -> Lambda $ \b -> a() -- Added fn call
--Unneeded in haskell:Ulazyfalse = Lambda $ \a -> Lambda $ \b -> b()

--ISN0 needs to select these lazy fns to be able to then call their selected
--Unneeded in haskell:lazyisn0 = Lambda $ \a -> a(Lambda $ \a -> LAZYfalse)(LAZYtrue)
-- Replace fns with above and convert selections to 0-arg lambdas
--facv2 = Lambda $ \a -> LAZYISN0(a)\
--            (lambda -> n1)\
--            (lambda -> mul(a)(FACV2(pred(a))))
-- The above works! But the explicit self-reference (with a name)
-- is an issue because it is technically not allowed since
-- there are no (assignment) names in the lambda-calculus.

-- As an intermediary step, have the recursive call be a var to pass in
-- and then make a call to itself outside the main body.
-- Make sure to follow the new API within the fn--
-- it now takes a fn f as an argument!
facv3proto = Lambda $ \f -> Lambda $ \a -> isn0 ! a !
            n1 !
            (mul ! a ! (f ! f ! (pred ! a)))
facv3 = facv3proto ! facv3proto -- Note Haskell is different here:FACV3 needs to be assigned before it can be called on itself
-- Note that factorial must be a fixed point function of factorial!
-- If you give FACV3 itself, you'll get FACV3 in return.

-- The solution is now much more obvious--
-- just call the Lambda $ \definition on itself.
facv4 = Lambda (\f -> Lambda $ \a -> isn0 ! a !
            n1 !
            (mul ! a ! (f ! f ! (pred ! a)))) !
        Lambda (\f -> Lambda $ \a -> isn0 ! a !
            n1 !
            (mul ! a ! (f ! f ! (pred ! a))))

-- There is now no reference to the assignment name anywhere in the body!
-- Equiv. with FACV4 = M(FACV3)

-- The Y-Combinator is a fixpoint fn
-- The Z-Combinator is a version of the Y-Combinator,
-- that makes the typical eagar evaluation behavior lazy.
-- Fixpoints of fn f are where f(x) = x
-- COS(0.739...) = 0.739...
-- SIN(0) = 0
-- Some fns have multiple fixpoints!
-- SQRT(1) = 1
-- SQRT(0) = 0
-- id(Anything) = Anything
-- Some fns don't have any fixpoints

-- The Y Fixed-Point Combinator works in lazy languages--e.g., Haskell
y = (Lambda $ \a ->
    (Lambda $ \b -> a ! (b ! b) ) !
    (Lambda $ \b -> a ! (b ! b) ))

yequiv = Lambda $ \a -> m ! (Lambda $ \b -> a ! (m ! b))

-- The Z Fixed-Point Combinator works in non-lazy languages--e.g., Python
z = (Lambda $ \a ->
    (Lambda $ \b -> a ! (Lambda $ \c -> b ! (b) ! (c)) ) !
    (Lambda $ \b -> a ! (Lambda $ \c -> b ! (b) ! (c)) ))

zequiv = Lambda $ \a -> m ! (Lambda $ \b -> a ! (Lambda $ \c -> m ! (b) ! (c)))

-- Rewrittern for Haskell:Note Python's lazy-evaluation for if/else statements
r = (Lambda $ \a -> Lambda $ \b -> if view b == 0 then View 1 else View ((view b) * (view a * ((view b)-1))))
-- Still needs Z to avoid infinite recursion loop
--FAC = Z(R) -- This works with number arguments

-- To use Z with only lambdas, make a naive recursive version
-- of factorial (like FACV3 above) where f is thought of as
-- itself rather than a separate argument to substitute in the body.
facproto = (Lambda $ \f -> Lambda $ \a -> isn0 ! a !
            (n1) !
            (mul ! a ! (f ! (pred ! a))))

-- These all work in Haskell
fac = y ! facproto
fac1 = yequiv ! facproto
fac2 = z ! facproto
fac3 = zequiv ! facproto


-- Fibunacci sequence
-- If n < 2 -> return n; else -> return fib(pred(n)) + fib(pred(pred(n)))
-- Lazy less than or equal
--Unneeded in haskell:lazyleq = Lambda $ \a -> Lambda $ \b -> LAZYISN0(sub(a)(b))


{-
FIBPROTO = (lambda f: lambda a: LAZYLEQ(a)(N1)\
            (lambda: a)\
            (lambda: ADD(f(PRED(a)))(f(PRED(PRED(a))))))
-}
fibproto = (Lambda $ \f -> Lambda $ \a -> leq ! a ! n1 !
            a !
            (add ! (f ! (pred ! a)) ! (f ! (pred ! (pred ! a)))))

-- These all work in Haskell
fib = y ! fibproto
fib1 = yequiv ! fibproto
fib2 = z ! fibproto
fib3 = zequiv ! fibproto


--Unneeded in haskell:lazynot = Lambda $ \a -> a(LAZYfalse)(LAZYtrue)
--Unneeded in haskell:lazygt = Lambda $ \a -> Lambda $ \b -> LAZYNOT(ISN0(sub(a)(b))) -- Note -> needs regular ISN0 to select as normal (i.e., *not* select and then call) within LAZYNOT fn
--LAZYGT = Lambda $ \a -> Lambda $ \b -> a(LAZYtrue)(Lambda $ \z -> LAZYfalse)(sub(a)(b)) -- Doesn't work
--Unneeded in haskell:lazylt = Lambda $ \a -> Lambda $ \b -> LAZYGT(b)(a)

-- DIVMODPAIR evaluates to a pair of two numbers, (a div b, a mod b)
-- DIVMODPAIR  ->= Y (λgqab. LT a b (PAIR q a) (g (sucC q) (sub a b) b)) 0

divmodproto = (Lambda $ \g -> Lambda $ \q -> Lambda $ \a -> Lambda $ \b ->
            --LAZYISN0(a)\
            lt ! a ! b !
            (v ! q ! a) !
            (g ! (suc ! q) ! (sub ! a ! b) ! b))

divmodpair = y ! divmodproto ! n0

divmodpairequiv = (Lambda $ \g -> Lambda $ \q -> Lambda $ \a -> Lambda $ \b ->
            lt ! a ! b !
            (v ! q ! a) !
            (g ! g ! (suc ! q) ! (sub ! a ! b) ! b)) !
            (Lambda $ \g -> Lambda $ \q -> Lambda $ \a -> Lambda $ \b ->
            lt ! a ! b !
            (v ! q ! a) !
            (g ! g ! (suc ! q) ! (sub ! a ! b) ! b)) ! n0

div = Lambda $ \a -> Lambda $ \b -> first ! (divmodpair ! a ! b)
mod = Lambda $ \a -> Lambda $ \b -> second ! (divmodpair ! a ! b)

-- The following two are alternative implementations to using the fixpoint combinator (at least explicitly)
-- λn. n (λfax. f (mul a x) (sucC x)) K 1 1
newfac = Lambda $ \n -> n ! (Lambda $ \f -> Lambda $ \a -> Lambda $ \x -> f ! (mul ! a ! x) ! (suc ! x)) ! k ! n1 ! n1

-- λn. n (λfab. f b (PLUS a b)) K 0 1
newfib =  Lambda $ \n -> n ! (Lambda $ \f -> Lambda $ \a -> Lambda $ \b -> f ! b ! (add ! a ! b)) ! k ! n0 ! n1

-- GCD  ->= (λgmn. LEQ m n (g n m) (g m n)) (Y (λgxy. ISzero y x (g y (MOD x y))))
gcd =  (Lambda $ \g -> Lambda $ \m -> Lambda $ \n -> leq ! m ! n ! (g ! n ! m) ! (g ! n ! m)) !
        (y ! (Lambda $ \g -> Lambda $ \x -> Lambda $ \y -> isn0 ! y ! x ! (g ! y ! (mod ! x ! y))))

-- Computability and Logic (C&L) 3rd ed. p 76
-- Primitive Recursion ->
-- h(x, 0) = f(x), h(x, suc(y)) = g(x, y, h(x, y))
-- Careful! We need to pass f and g along in the recursive call!
prproto = Lambda $ \h -> Lambda $ \f -> Lambda $ \g -> Lambda $ \x -> Lambda $ \y ->
        isn0 ! y !
        (f ! x) !
        (g! (x) ! (pred ! (y)) ! (h ! (f) ! (g) ! (x) ! (pred ! (y))))
pr = y ! prproto

-- C&L 3rd ed. p 77--Extending pr to single or(XOR) more than two variables
-- Primitive Recursion for defining single var fns ->
-- h(0) = 0, or 1, or 2 ..., h(suc(y)) = g(y, h(y))
prx1proto = Lambda $ \h -> Lambda $ \f -> Lambda $ \g -> Lambda $ \y ->
        isn0 ! y !
        (f) !
        (g ! (pred ! (y)) ! (h ! (f) ! (g) ! (pred ! (y))))
prx1 = y ! prx1proto


-- C&L 3rd ed. p 77--Extending pr to single or(XOR) more than two variables
-- Primitive Recursion for defining triple var fns ->
-- h(x1, x2, 0) = f(x1, x2), h(x1, x2, suc(y)) = g(x1, x2, y, h(x1, x2, y))
prx3proto = Lambda $ \h -> Lambda $ \f -> Lambda $ \g -> Lambda $ \x1 -> Lambda $ \x2 -> Lambda $ \y ->
        isn0 ! y !
        f ! x1 ! x2 !
        (g ! (x1) ! (x2) ! (pred ! (y)) ! (h ! (f) ! (g) ! (x1) ! (x2) ! (pred ! (y))))
prx3 = y ! prx3proto

-- Quad and greater than 4-tuple pr functions could be defined from here ....


-- More id fns, named according to C&L 3rd ed.
-- Note -> no need to do lazy eval, because lazy booleans will call recursive step only if needed (i.e. lazily)
id11 = Lambda $ \a -> a
id21 = Lambda $ \a -> Lambda $ \b -> a
id22 = Lambda $ \a -> Lambda $ \b -> b
id31 = Lambda $ \a -> Lambda $ \b -> Lambda $ \c -> a
id32 = Lambda $ \a -> Lambda $ \b -> Lambda $ \c -> b
id33 = Lambda $ \a -> Lambda $ \b -> Lambda $ \c -> c

-- Composition C&L 3rd ed. p 75
-- Looks like we need to implement particular versions of Cm[f,g] according to the number 
-- of args g takes--as well as amount of g fns themselves if more than one is used.
-- So g takes 3 args below ->
cnx3 = Lambda $ \f -> Lambda $ \g -> Lambda $ \x -> Lambda $ \y -> Lambda $ \z -> f ! (g ! (x) ! (y) ! (z))
-- g takes 2 args ->
cnx2 = Lambda $ \f -> Lambda $ \g -> Lambda $ \x -> Lambda $ \y -> f ! (g ! (x) ! (y))
-- Two g args, three x args
cng2x3 = Lambda $ \f -> Lambda $ \g -> Lambda $ \h -> Lambda $ \x -> Lambda $ \y -> Lambda $ \z -> f ! (g ! (x) ! (y) ! (z)) ! (h ! (x) ! (y) ! (z))
-- Two g args, one x arg -> NOT USED IN THIS FILE
cn2g = Lambda $ \f -> Lambda $ \g -> Lambda $ \h -> Lambda $ \x -> f ! (g ! (x)) ! (h ! (x))
-- Two g args, two x args ->
cng2x2 = Lambda $ \f -> Lambda $ \g -> Lambda $ \h -> Lambda $ \x -> Lambda $ \y -> f ! (g ! (x) ! (y)) ! (h ! (x) !(y))
-- Zero Primitive Recursive fn
zero = Lambda $ \a -> a ! (k ! (n0)) ! (n0)

-- x + 2
add2 = bC ! (suc) ! (suc)
-- x + 3
add3 = bC ! (suc) ! (add2)

-- Now we can define functions in terms of Primitive Recursive functions,
-- and explicitly according to how C&L 3rd ed. defines them.
addpr = pr ! (id11) ! (cnx3 ! (suc) ! (id33))
subpr = pr ! (id11) ! (cnx3 ! (pred) ! (id33))
mulpr = pr ! (zero) ! (cng2x3 ! (addpr) ! (id31) ! (id33))
powpr = pr ! (bC ! (suc) ! (zero)) ! (cng2x3 ! (mulpr) ! (id31) ! (id33))
-- super exponentiation
-- c&l 3rd ed. p 60
-- sup(2,4) = (2 ** (2 ** (2 ** 2))) = (2 ** ( 2 ** 4)) = 2 ** 16
sup = pr ! (bC ! (suc) ! (zero)) ! (cng2x3 ! (t) ! (id31) ! (id33)) -- using t here gets sup(2)(4) before recursion depth is reached
facpr = prx1 ! (n1) ! (cng2x2 ! (mul) ! (cnx2 ! (suc) ! (id21)) ! (id22))
predpr = prx1 ! (n0) ! (id21)
signum = prx1 ! (n0) ! (cnx2 ! (suc) ! (cnx2 ! (zero) ! (id21)))
notsignum = prx1 ! (n1) ! (cnx2 ! (zero) ! (id21))
-- Makes church numeral from a natural number.
makeNum :: Integer -> Expression
makeNum n =
    let
    -- Start with N0
    result = Lambda $ \a -> Lambda $ \b -> b
    go expr acc
        | acc == 0  = expr
        | otherwise = go ((Lambda $ \a  -> Lambda $ \b -> Lambda $ \c -> b ! (a ! (b) ! (c))) ! (expr)) (acc - 1)

    in go result n
{-
    for i in range(n) ->

        -- Apply suc to result
        result = (Lambda $ \a  -> Lambda $ \b -> Lambda $ \c -> b(a(b)(c)))(result)

    return result



def eval_boolean(church_boolean) ->
    """
    Evaluates Church Boolean to a Python boolean.
    Works only if true and false are assigned to their
    respective Church Booleans.
    """

    if church_boolean == true ->
        return True
    if church_boolean == false ->
        return False

    print("Boolean evaluation failed! Maybe input was not a Church Boolean?")
    return None

def eval_numeral(church_numeral) ->
    """
    Evaluates church numerals to a Python number.
    """

    n0 = 0
    suc = Lambda $ \a -> a + 1

    return church_numeral(suc)(n0)

def make_numeral(n) ->
    """
    Makes church numeral from a natural number.
    """
    -- Start with N0
    result = Lambda $ \a -> Lambda $ \b -> b

    for i in range(n) ->

        -- Apply suc to result
        result = (Lambda $ \a  -> Lambda $ \b -> Lambda $ \c -> b(a(b)(c)))(result)

    return result

def eval_pair(pair) ->
    return [eval_numeral(FIRST(pair)), eval_numeral(SECOND(pair))]

def eval_triple(triple) ->
    return [eval_numeral(V3FIRST(triple)),eval_numeral(V3SECOND(triple)),eval_numeral(V3THIRD(triple))]
-}
