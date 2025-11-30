We port the context representation library from the paper "Formalized meta-theory of sequent calculi for linear logics" (https://doi.org/10.1016/j.tcs.2019.02.023)
from Abella to Coq/Rocq.

To compile, run 

``` sh
    coq_makefile -f _CoqProject -o CoqMakefile
    make -f CoqMakefile_
```
