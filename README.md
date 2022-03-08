# lambda-calculus

Implements basic combinator functions, primitive recursive functions,
and from there, the possibility of all computable functions in
the untyped lambda calculus in Python.

Contains documentation documentation about working around Python's 
eager evaluation in implementing recursion.

Convert lambda (Church) numerals to Python numbers and vice versa with:
eval_numeral(church_numeral)
make_numeral(n)

Similarly evaluate booleans with eval_boolean(church_boolean).

Church numerals N0-N32 are defined for convenience.

Evaluate Church operator functions by passing them as an argument
in their proper eval argument: e.g. eval_numeral(MUL(N3)(N5))
