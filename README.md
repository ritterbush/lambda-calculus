# lambda-calculus

### Haskell

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

### Python

Implements basic combinator functions, primitive recursive functions,
and from there, the possibility of all computable functions in the
untyped lambda calculus in Python.

Contains documentation documentation about working around Python's
eager evaluation in implementing recursion.

Convert Church Numerals to Python integers and vice versa with:
    decode_num(church_numeral)
    make_num(n)

Church numerals N0-N32 are defined for convenience.

Similarly convert Church Booleans to Python booleans with:
    decode_bool(church_boolean)

Evaluate Church operator functions by passing them as an argument
in their proper decode function (apply functions to their arguments with parentheses); e.g.
    decode_num (MUL(SUC(N2))(ADD(N2)(N2)))        # == 12
    decode_bool (AND(NOT(NOT(NOT(FALSE))))(TRUE)) # == True

To use, enter the following into a terminal:
    python3 -i lambda_calculus.py
