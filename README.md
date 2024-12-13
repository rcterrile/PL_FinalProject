# PL_FinalProject

This project aims to build a simple low-level stack-based language in Coq. The language features integers and boolean values as well as arithmetic and boolean operations such as:
```
Add
Sub
Mul
And
Not
```

Along with these simple operations, the language also features variable assignments which can store numeric or boolean values. Included in the code is a compiler from Imp to this low-level language along with several proofs of bisimulation for some operations. Because the language does not feature every boolean operation seen in Imp, it cannot handle if statements or while loops, but it can fully convert Imp programs that rely on assignments, sequences, and updates.
