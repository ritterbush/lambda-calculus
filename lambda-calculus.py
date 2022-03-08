"""
Implements basic combinator functions, primitive recursive functions, 
and from there, the possibility of all computable functions in the 
untyped lambda calculus in Python.

Contains documentation documentation about working around Python's
eager evaluation in implementing recursion.

Convert lambda (Church) numerals to Python numbers and vice versa
with: eval_numeral(church_numeral) make_numeral(n)

Similarly evaluate booleans with eval_boolean(church_boolean).

Church numerals N0-N32 are defined for convenience.

Evaluate Church operator functions by passing them as an argument
in their proper eval argument: e.g. eval_numeral(MUL(N3)(N5))
"""

# ID fn
I = lambda a: a # id in Haskell
# ID 2,1 (given 2 args, return arg 1)
K = lambda a: lambda b: a # const in Haskell: const 7 "anything" == 7
# ID 2,2 (given 2 args, return arg 2)
KI_PRIMITIVE= lambda a: lambda b: b
KI = K(I) # const id in Haskell

# "lowercase omega" or "self application" combinator
M = lambda a: a(a) # Cannot define in Haskell
#M(M) is the "uppercase omega"; reduces to itself; loops/recurses forever

# Swaps arguments
C = lambda a: lambda b: lambda c: a(c)(b) # flip in Haskell: flip const 'a' 'b' == 'b'
# C(K) is equiv to K(I)

# Church encodings (booleans)
TRUE = K
FALSE = KI
# C is extentionally equivalent (same inputs/outputs) with NOT
NOT = lambda a: a(FALSE)(TRUE)
NOTTRUE = C(TRUE) # Extentionally equivalent with NOT(TRUE)
NOTFALSE = C(FALSE) # Extentionally equalent with NOT(FALSE)
# Study what intentionally equality may amount to--fns are defined differently
AND = lambda a: lambda b: a(b)(a) # If a is false, false fn results; if a is true, b fn results
OR = lambda a: lambda b: a(a)(b) # If a is true, true fn results; if a is false, b fn results
# M is extentionally equivalent with OR
# NOT (C) and OR (M) grant all other booleans of propositional logic
# Boolean Equality
BEQUALS = lambda a: lambda b: a(b)(NOT(b))

# Church numerals
N0 = lambda a: lambda b: b # Note that the a is still needed: apply a to b zero times
# N0 = FALSE = KI (equivelent in both senses)
N1 = lambda a: lambda b: a(b) # I* Applies ab to ab
N2 = lambda a: lambda b: a(a(b)) # Not like I, since it doubles application of a on b
# ...

# For a successor fn that takes one of the above numerals as an arg
# just copy the a position argument (of above, b below) out front to be applied once more.
SUC = lambda a : lambda b: lambda c: b(a(b)(c))

n0_readable = 0
suc_readable = lambda a: a + 1

N3 = SUC(N2)
# Function composition combinator; "bluebird combinator"
# f(g(a))
# Also pipeline: apply g to a and pipe the result to f.
# In Haskell this is built in as the '.': odd = not . even
# Can also use it in prefix notation in Haskell with parens: (.)
B = lambda a: lambda b: lambda c: a(b(c))

SUCB = lambda a: lambda b: B(b)(a(b)) # Alternative successor fn, using B
ADD = lambda a: lambda b: a(SUC)(b)
# To mul, apply fn c b times, and do this a times; this is B!
MUL = lambda a: lambda b: lambda c: a(b(c))
# MUL just is B (they are alpha equivalent)
# Interesting to see how B also composes a successor fn

N4 = ADD(N2)(N2)
N5 = SUC(ADD(N2)(N2))
N6 = MUL(N3)(N2)
N7 = SUC(MUL(N3)(N2))

# Thrush
# Equivalent with CI
# flip id in Haskell
# Equivalent with the POW fn!
T = lambda a: lambda b: b(a)

N8 = T(N2)(N3)
N9 = T(N3)(N2)

# Is/Equals zero fn
ISN0 = lambda a: a(K(FALSE))(TRUE)

# Vireo, the smallest data structure in lambda calculus
# Equiv with BCT; in Haskell: flip . flip id
# The Church pairing fn, which pairs two arguments
V = lambda a: lambda b: lambda c: c(a)(b)

# Holds on to I and M as arguments to access
VIM = V(I)(M)
# Now access arg1 with K, arg2 with KI
assert VIM(K) == I
assert VIM(KI) == M

# Used on pairs which hold arguments, such as VIM
FIRST = lambda a: a(K)
SECOND = lambda a: a(KI)

# Takes a pair, and returns pair of second item,
# and second item plus 1
PHI = lambda a: V(SECOND(a))(SUC(SECOND(a)))

# Applying PHI to (N0, N0), we get (N0, N1)
# Applying PHI to (N0, N0) 8 times, we get (N7, N8)
# Notice that the first item is N7, the PRED of N8!
PRED = lambda a: FIRST(a(PHI)(V(N0)(N0)))

# Original, more complcated predecessor fn
PREDEQUIV = lambda n: n\
            (lambda g: ISN0(g(N1))(I)(B(SUC)(g)))\
            (K(N0))(N0)

# First arg is item to set and second arg is a Church pair
SETFIRST = lambda a: lambda b: V(a)(SECOND(b))
SETSECOND = lambda a: lambda b: V(FIRST(b))(a)

SUB = lambda a: lambda b: b(PRED)(a)

# Less than or equal
LEQ = lambda a: lambda b: ISN0(SUB(a)(b))
# Equals
EQ = lambda a: lambda b: AND(ISN0(SUB(a)(b)))(ISN0(SUB(b)(a)))
# Greater than
GT = lambda a: lambda b: NOT(ISN0(SUB(a)(b)))
# Less than
LT = lambda a: lambda b: NOT(ISN0(SUB(b)(a)))

BLACKBIRD = B(B)(B)
GTEQUIV = BLACKBIRD(NOT)(LEQ)

N10 = PRED(SUC(SUC(N9)))
N11 = SUC(SUC(N9))
N12 = MUL(N3)(N4)
N13 = SUC(MUL(N3)(N4))
N14 = SUC(N13)
N15 = SUC(N14)

# Triple data structure
V3 = lambda a: lambda b: lambda c: lambda d: d(a)(b)(c)
V3FIRST = lambda v: v(lambda a: lambda b: lambda c: a)
V3SECOND = lambda v: v(lambda a: lambda b: lambda c: b)
V3THIRD = lambda v: v(lambda a: lambda b: lambda c: c)

# Sub first and second and store as first, keep second, increment third.
# Can be used with a loop for a div fn that returns the third at the end.
# Just a prototype.
PHIDIV = lambda a: V3(SUB(V3FIRST(a))(V3SECOND(a)))(V3SECOND(a))(SUC(V3THIRD(a)))


# IMPLEMENTING RECURSION.

# Attempt a FAC fn with explicit recursive call.
# Rec. limit reached because Python won't short-circuit
# and so WILL evaluate the last line even when ISNO(a)
# is FALSE and would just select (N1). Makes sense--
# Python wouldn't know what our FALSE fn does ahead of
# such evaluations, as it does know with, say, 'False and 4 / 0'.
FACV1 = lambda a: ISN0(a)\
            (N1)\
            (MUL(a)(FACV1(PRED(a))))
# Above, the fn repeats evaluating the last line when a is N0
# We can get around this by delaying the evaluation (implementing
# our own lazy evaluation in place of the eager evaluation).
# We do this by reimplementing our true and false fns to select
# and then call as a fn what is selected. This requires that
# what gets selected be evaluated after being called; which is
# done by just converting the selections to be zero-argument lambdas.

LAZYTRUE = lambda a: lambda b: a() # Added fn call
LAZYFALSE = lambda a: lambda b: b()
#ISN0 needs to select these lazy fns to be able to then call their selected
LAZYISN0 = lambda a: a(lambda a: LAZYFALSE)(LAZYTRUE)
# Replace fns with above and convert selections to 0-arg lambdas
FACV2 = lambda a: LAZYISN0(a)\
            (lambda: N1)\
            (lambda: MUL(a)(FACV2(PRED(a))))
# The above works! But the explicit self-reference (with a name)
# is an issue because it is technically not allowed since
# there are no (assignment) names in the lambda-calculus.

# As an intermediary step, have the recursive call be a var to pass in
# and then make a call to itself outside the main body.
# Make sure to follow the new API within the fn--
# it now takes a fn f as an argument!
FACV3 = lambda f: lambda a: LAZYISN0(a)\
            (lambda: N1)\
            (lambda: MUL(a)(f(f)(PRED(a))))
FACV3 = FACV3(FACV3) # FACV3 needs to be assigned before it can be called on itself
# Note that factorial must be a fixed point function of factorial!
# If you give FACV3 itself, you'll get FACV3 in return.

# The solution is now much more obvious--
# just call the lambda definition on itself.
FACV4 = (lambda f: lambda a: LAZYISN0(a)\
            (lambda: N1)\
            (lambda: MUL(a)(f(f)(PRED(a)))))\
        (lambda f: lambda a: LAZYISN0(a)\
            (lambda: N1)\
            (lambda: MUL(a)(f(f)(PRED(a)))))
# There is now no reference to the assignment name anywhere in the body!
# Equiv. with FACV4 = M(FACV3)

# The Y-Combinator is a fixpoint fn
# The Z-Combinator is a version of the Y-Combinator,
# that makes the typical eagar evaluation behavior lazy.
# Fixpoints of fn f are where f(x) = x
# COS(0.739...) = 0.739...
# SIN(0) = 0
# Some fns have multiple fixpoints!
# SQRT(1) = 1
# SQRT(0) = 0
# ID(Anything) = Anything
# Some fns don't have any fixpoints

# The Y Fixed-Point Combinator works in lazy languages
Y = (lambda a:
    (lambda b: a(b(b)) )
    (lambda b: a(b(b)) ))

YEQUIV = lambda a: M(lambda b: a(M(b)))

# The Z Fixed-Point Combinator works in non-lazy languages--e.g., Python
Z = (lambda a:
    (lambda b: a(lambda c: b(b)(c)) )
    (lambda b: a(lambda c: b(b)(c)) ))

ZEQUIV = lambda a: M(lambda b: a(lambda c: M(b)(c)))

# Note Python's lazy-evaluation for if/else statements
R = (lambda a: lambda b: 1 if b == 0 else b*a(b-1))
# Still needs Z to avoid infinite recursion loop
#FAC = Z(R) # This works with number arguments

# To use Z with only lambdas, make a naive recursive version
# of factorial (like FACV3 above) where f is thought of as
# itself rather than a separate argument to substitute in the body.
FACPROTO = (lambda f: lambda a: LAZYISN0(a)\
            (lambda: N1)\
            (lambda: MUL(a)(f(PRED(a)))))

FAC = Z(FACPROTO)
#FAC = ZEQUIV(FACPROTO)

# Fibunacci sequence
# If n < 2: return n; else: return fib(pred(n)) + fib(pred(pred(n)))
# Lazy less than or equal
LAZYLEQ = lambda a: lambda b: LAZYISN0(SUB(a)(b))

FIBPROTO = (lambda f: lambda a: LAZYLEQ(a)(N1)\
            (lambda: a)\
            (lambda: ADD(f(PRED(a)))(f(PRED(PRED(a))))))

FIB = Z(FIBPROTO)
#FIB = ZEQUIV(FIBPROTO)

LAZYNOT = lambda a: a(LAZYFALSE)(LAZYTRUE)
LAZYGT = lambda a: lambda b: LAZYNOT(ISN0(SUB(a)(b))) # Note: needs regular ISN0 to select as normal (i.e., *not* select and then call) within LAZYNOT fn
#LAZYGT = lambda a: lambda b: a(LAZYTRUE)(lambda z: LAZYFALSE)(SUB(a)(b)) # Doesn't work
LAZYLT = lambda a: lambda b: LAZYGT(b)(a)

# DIVMODPAIR evaluates to a pair of two numbers, (a div b, a mod b)
# DIVMODPAIR := Y (λgqab. LT a b (PAIR q a) (g (SUCC q) (SUB a b) b)) 0

DIVMODPROTO = (lambda g: lambda q: lambda a: lambda b:\
            #LAZYISN0(a)\
            LAZYLT(a)(b)\
            (lambda: V(q)(a))\
            (lambda: g(SUC(q))(SUB(a)(b))(b)))

DIVMODPAIR = Z(DIVMODPROTO)(N0)

DIVMODPAIREQUIV = ((lambda g: lambda q: lambda a: lambda b:\
            LAZYLT(a)(b)\
            (lambda: V(q)(a))\
            (lambda: g(g)(SUC(q))(SUB(a)(b))(b))))\
            ((lambda g: lambda q: lambda a: lambda b:\
            LAZYLT(a)(b)\
            (lambda: V(q)(a))\
            (lambda: g(g)(SUC(q))(SUB(a)(b))(b))))(N0)

DIV = lambda a: lambda b: FIRST(DIVMODPAIR(a)(b))
MOD = lambda a: lambda b: SECOND(DIVMODPAIR(a)(b))

# The following two are alternative implementations to using the fixpoint combinator (at least explicitly)
# λn. n (λfax. f (MUL a x) (SUCC x)) K 1 1
NEWFAC = lambda n: n(lambda f: lambda a: lambda x: f(MUL(a)(x))(SUC(x)))(K)(N1)(N1)

# λn. n (λfab. f b (PLUS a b)) K 0 1
NEWFIB =  lambda n: n(lambda f: lambda a: lambda b: f(b)(ADD(a)(b)))(K)(N0)(N1)

# GCD := (λgmn. LEQ m n (g n m) (g m n)) (Y (λgxy. ISZERO y x (g y (MOD x y))))
GCD =  (lambda g: lambda m: lambda n: LEQ(m)(n)((g)(n)(m))((g)(n)(m)))\
        (Z(lambda g: lambda x: lambda y: LAZYISN0(y)(lambda: x)(lambda: (g)(y)(MOD(x)(y)))))

# Computability and Logic (C&L) 3rd ed. p 76
# Primitive Recursion:
# h(x, 0) = f(x), h(x, suc(y)) = g(x, y, h(x, y))
# Careful! We need to pass f and g along in the recursive call!
PRPROTO = lambda h: lambda f: lambda g: lambda x: lambda y:\
        LAZYISN0(y)\
        (lambda: f(x))\
        (lambda: g(x)(PRED(y))(h(f)(g)(x)(PRED(y))))
PR = Z(PRPROTO)

# C&L 3rd ed. p 77--Extending PR to single or(XOR) more than two variables
# Primitive Recursion for defining single var fns:
# h(0) = 0, or 1, or 2 ..., h(suc(y)) = g(y, h(y))
PRX1PROTO = lambda h: lambda f: lambda g: lambda y:\
        LAZYISN0(y)\
        (lambda: f)\
        (lambda: g(PRED(y))(h(f)(g)(PRED(y))))
PRX1 = Z(PRX1PROTO)


# C&L 3rd ed. p 77--Extending PR to single or(XOR) more than two variables
# Primitive Recursion for defining triple var fns:
# h(x1, x2, 0) = f(x1, x2), h(x1, x2, suc(y)) = g(x1, x2, y, h(x1, x2, y))
PRX3PROTO = lambda h: lambda f: lambda g: lambda x1: lambda x2: lambda y:\
        LAZYISN0(y)\
        (lambda: f(x1)(x2))\
        (lambda: g(x1)(x2)(PRED(y))(h(f)(g)(x1)(x2)(PRED(y))))
PRX3 = Z(PRX3PROTO)

# Quad and greater than 4-tuple PR functions could be defined from here ....


# More ID fns, named according to C&L 3rd ed.
# Note: no need to do lazy eval, because lazy booleans will call recursive step only if needed (i.e. lazily)
ID11 = lambda a: a
ID21 = lambda a: lambda b: a
ID22 = lambda a: lambda b: b
ID31 = lambda a: lambda b: lambda c: a
ID32 = lambda a: lambda b: lambda c: b
ID33 = lambda a: lambda b: lambda c: c

# Composition C&L 3rd ed. p 75
# Looks like we need to implement particular versions of Cm[f,g] according to the number 
# of args g takes--as well as amount of g fns themselves if more than one is used.
# So g takes 3 args below:
CNX3 = lambda f: lambda g: lambda x: lambda y: lambda z: f(g(x)(y)(z))
# g takes 2 args:
CNX2 = lambda f: lambda g: lambda x: lambda y: f(g(x)(y))
# Two g args, three x args
CNG2X3 = lambda f: lambda g: lambda h: lambda x: lambda y: lambda z: f(g(x)(y)(z))(h(x)(y)(z))
# Two g args, one x arg: NOT USED IN THIS FILE
CN2G = lambda f: lambda g: lambda h: lambda x: f(g(x))(h(x))
# Two g args, two x args:
CNG2X2 = lambda f: lambda g: lambda h: lambda x: lambda y: f(g(x)(y))(h(x)(y))
# Zero Primitive Recursive fn
ZERO = lambda a: a(K(N0))(N0)

# x + 2
ADD2 = B(SUC)(SUC)
# x + 3
ADD3 = B(SUC)(ADD2)

# Now we can define functions in terms of Primitive Recursive functions,
# and explicitly according to how C&L 3rd ed. defines them.
ADDPR = PR(ID11)(CNX3(SUC)(ID33))
SUBPR = PR(ID11)(CNX3(PRED)(ID33))
MULPR = PR(ZERO)(CNG2X3(ADDPR)(ID31)(ID33))
POWPR = PR(B(SUC)(ZERO))(CNG2X3(MULPR)(ID31)(ID33))
# Super exponentiation
# C&L 3rd ed. p 60
# sup(2,4) = (2 ** (2 ** (2 ** 2))) = (2 ** ( 2 ** 4)) = 2 ** 16
SUP = PR(B(SUC)(ZERO))(CNG2X3(T)(ID31)(ID33)) # Using T here gets SUP(2)(4) before recursion depth is reached
FACPR = PRX1(N1)(CNG2X2(MUL)(CNX2(SUC)(ID21))(ID22))
PREDPR = PRX1(N0)(ID21)
SIGNUM = PRX1(N0)(CNX2(SUC)(CNX2(ZERO)(ID21)))
NOTSIGNUM = PRX1(N1)(CNX2(ZERO)(ID21))


def eval_boolean(church_boolean):
    """
    Evaluates Church Boolean to a Python boolean.
    Works only if TRUE and FALSE are assigned to their
    respective Church Booleans.
    """

    if church_boolean == TRUE:
        return True
    if church_boolean == FALSE:
        return False

    print("Boolean evaluation failed! Maybe input was not a Church Boolean?")
    return None

def eval_numeral(church_numeral):
    """
    Evaluates church numerals to a Python number.
    """

    n0 = 0
    suc = lambda a: a + 1

    return church_numeral(suc)(n0)

def make_numeral(n):
    """
    Makes church numeral from a natural number.
    """
    # Start with N0
    result = lambda a: lambda b: b

    for i in range(n):

        # Apply SUC to result
        result = (lambda a : lambda b: lambda c: b(a(b)(c)))(result)

    return result

def eval_pair(pair):
    return [eval_numeral(FIRST(pair)), eval_numeral(SECOND(pair))]

def eval_triple(triple):
    return [eval_numeral(V3FIRST(triple)),eval_numeral(V3SECOND(triple)),eval_numeral(V3THIRD(triple))]

