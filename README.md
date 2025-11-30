We port the context representation library from the paper "Formalized meta-theory of sequent calculi for linear logics" (https://doi.org/10.1016/j.tcs.2019.02.023)
from Abella to Coq/Rocq.

To compile, run 

``` sh
    coq_makefile -f _CoqProject -o CoqMakefile
    make -f CoqMakefile_
```

Some notes about observations/decisions made are in:

https://docs.google.com/document/d/e/2PACX-1vQw71-1sMkQU0xtR4KDcSZrzBy25di2cXN9nP1q78wrKi_hvpqbuR34rJ27H9QZ48AsR_GVduwOI2LN/pub
