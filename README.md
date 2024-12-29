



## Table:

The library succesfully compiles with the Coq compiler ?????.
-  `coq_makefile -f _CoqProject -o Makefile` to create the Makefile
-  `make` to compile

| | File    | Description |
| -------- | -------- | ------- |
| 1 | `src/sim.v` | Simple lemmas deriving from the library |
| 2 | `src/header.v` | Defines constructors needed to define specific session type constructors and lemmas relating to them |
| 3 | `src/expr.v` | Definition of session expressions and sorts | 
| 4 | `src/process.v` | Definition of session processes and some helper lemmas |
| 5 | `src/local.v` | Definition of Local Tree / Types and subtyping, along with properties relating to them | 
| 6 | `src/global.v` | Definition of Global Tree / Types and properties relating to them |
| 7 | `src/gttreeh.v` | Definition of Global Type Tree Context Holes and related properties | 
| 8 | `src/part.v` | Definition of participants and related properties |
| 9 | `src/balanced.v` | Definition of balanced global trees and related properties | 
| 10 | `src/typecheck.v` | Definition of typing rules for expressions and processes, with related properties |
| 11 | `src/step.v` | Definition of Global Trees taking a step |
| 12 | `src/merge.v` | Definition of the merging operator and related properties |
| 13 | `src/projection.v` | Definition of projection |
| 14 | `src/session.v` | Definitions related to sessions |
| 15 | `lemma/inversion.v` | Inversion Lemma for processes |
| 16 | `lemma/inversion_expr.v` | Inversion Lemma for expressions |
| 17 | `lemma/substitution_helper.v` | Helper functions for substitution lemma |
| 18 | `lemma/substitution.v` | Substitution Lemma for process and expression variables |
| 19 | `lemma/decidable_helper.v` | Helper functions relating to participant decidability |
| 20 | `lemma/decidable.v` | Lemmas regarding participant decidability |
| 21 | `lemma/expr.v` | Lemmas regarding expression evaluation |
| 22 | `lemma/part.v` | Lemmas regarding participants on subtrees |
| 23 | `lemma/step.v` | Lemmas regarding well-formedness of global trees after taking a step |
| 24 | `lemma/projection_helper.v` | Helper functions for projection related lemmas |
| 25 | `lemma/projection.v` | Lemmas regarding projections after global trees take a step | 
| 26 | `lemma/main_helper.v` | Helper functions for main theorems |
| 27 | `lemma/main.v` | Main Theorems |

