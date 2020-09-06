# Differustiation

A simple program that differentiates mathematical expressions. May or may not produce correct results. Based on the methods outlined [here](http://www.math.wpi.edu/IQP/BVCalcHist/calc5.html).

## Usage
The program outputs the derivative of the expression in its second argument with respect to the variable given as its first argument. The first argument should be a single letter and the second can be any valid expression.

Some examples
```
cargo run v v^-5
```
Will produce `(-5 / (v ^ 6))` as output.
```
cargo run x "x*ln(x+x)"
```
Will produce `(1 + ln((2*x)))` as output.
```
cargo run y y+1^y*22*y*x
```
Will produce `(1 + (22*x))` as output.
```
cargo run x "cos(x)^(a+b*x)"
```
Will produce `((cos(x) ^ (a + (b*x)))*(((-1*sin(x)*(a + (b*x))) / cos(x)) + (b*ln(cos(x)))))` as output.

Expressions are different elements seperated by the operators `+` (for addition),`-` (for subtraction),`*`(for multiplication),`/` (for division) and `^` (for exponentiation). Possible elements are numbers (of the form `123` or `123.456`), single letters to represent variables, or sequences of letters with an expression within parentheses to represent functions (`fun(a+b+c)`). You can use parentheses to be explicit about how expressions are evaluated too (`(x+y)*z` to multiply `z` by the sum of `x` and `y`). 

Currently only the `ln`, `sin` and `cos` functions are differentiated, other functions will just be returned as is.
