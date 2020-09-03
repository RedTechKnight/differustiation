# Differustiation

A simple program that differentiates mathematical expressions. May or may not produce correct results. Based on the methods outlined [here](http://www.math.wpi.edu/IQP/BVCalcHist/calc5.html).

## Usage
Some examples
```
cargo run v v^-5
```
```
cargo run x "x*ln(x+x)"
```
```
cargo run y y+1^y*22*y*x
```
```
cargo run x "cos(x)^(a+b*x)"
```

Always takes two parameters, first one is strictle a single letter to represent the variable of differentiation, second parameter is the expression to differentiate. 

Expressions are different elements seperated by the operators `+` (addition),`-` (subtraction),`*`(multiplication),`/` (division) and `^` (exponentiation). Possible elements are numbers (of the form `123` or `123.456`), single letters to represent variables, or sequnces of letters with an expression within parentheses to represent functions (`fun(a+b+c)`). You can use parentheses as you'd usually expect too.

Currently only the `ln`, `sin` and `cos` functions are differentiated, other functions will just be returned as is.
