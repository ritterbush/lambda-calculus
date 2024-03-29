# lambda-calculus

### Haskell

Implements basic combinator functions, primitive recursive functions,
and from there, the possibility of all computable functions in the
untyped lambda calculus in Haskell.

Uses a custom Haskell data type to work around type errors from many basic combinators.

Convert Church Numerals to Haskell Integers and vice versa with:

    decodeNum(church_numeral)
    makeNum(n)

Church Numerals `n0`-`n32` are defined for convenience.

Similarly convert Church Booleans to Haskell Bools with:

    decodeBool(church_boolean)

Evaluate Church operator functions by passing them as an argument
in their proper decode function (apply functions to their arguments with '!'); e.g.

    decodeNum (mul ! (suc ! n2) ! (add ! n2 ! n2))      -- == 12
    decodeBool (and ! (not ! not ! not ! false) ! true) -- == True

The typical operators such as `and` `or` `not` `add` `sub` `mul` `div` `mod` `fac` are defined, plus many more found in the source code. 
To use, enter the following into a terminal:

    ghci
    :l LambdaCalculus

### Python

Implements basic combinator functions, primitive recursive functions,
and from there, the possibility of all computable functions in the
untyped lambda calculus in Python.

Contains documentation about working around Python's
eager evaluation in implementing recursion.

Convert Church Numerals to Python integers and vice versa with:

    decode_num(church_numeral)
    make_num(n)

Church Numerals `N0`-`N32` are defined for convenience.

Similarly convert Church Booleans to Python booleans with:

    decode_bool(church_boolean)

Evaluate Church operator functions by passing them as an argument
in their proper decode function (apply functions to their arguments with parentheses); e.g.

    decode_num (MUL(SUC(N2))(ADD(N2)(N2)))        # == 12
    decode_bool (AND(NOT(NOT(NOT(FALSE))))(TRUE)) # == True

The typical operators such as `AND` `OR` `NOT` `ADD` `SUB` `MUL` `DIV` `MOD` `FAC` are defined, plus many more found in the source code.
To use, enter the following into a terminal:

    python3 -i lambda-calculus.py
