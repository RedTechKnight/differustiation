# Differustiation

A simple program that differentiates mathematical expressions. Still very incomplete (and may not produce correct results). Based on the methods outlined [here](http://www.math.wpi.edu/IQP/BVCalcHist/calc5.html)

## Usage
Basic example
```bash 
cargo run x "x*ln(x+x)"
```
Not much else it can do. Output isn't simplified or easily human readable, can only differentiate `ln`, `cos` and `sin` functions, parser is very basic.
