# SMPST-SR-SMER
Subject Reduction + Progress + Type Safety of synchronious multiparty session types (SMPST) with Plain Merging in Coq


| File    | Description |
| -------- | ------- |
| src/sim.v | Simple lemmas deriving from the library |
| src/header.v | Defines constructors needed to define specific session type constructors and lemmas relating to them |
| src/expr.v | Definition of session expressions and sorts | 
| src/process.v | Definition of session processes and some helper lemmas |
| src/local.v | Definition of Local Tree / Types and subtyping, along with properties relating to them | 
| src/global.v | Definition of Global Tree / Types and properties relating to them |
| src/gttreeh.v | Definition of Global Type Tree Context Holes and related properties | 
| src/part.v | Definition of participants and related properties |
| src/balanced.v | Definition of balanced global trees and related properties | 
| src/typecheck.v | Definition of typing rules for expressions and processes, with related properties |
| src/step.v | Definition of Global Trees taking a step |
| src/merge.v | Definition of the merging operator and related properties |
| src/projection.v | Definition of projection |
| src/session.v | Definitions related to sessions |
| lemma/inversion.v | Inversion Lemma for processes |
| lemma/inversion_expr.v | Inversion Lemma for expressions |
| lemma/substitution_helper.v | Helper functions for substitution lemma |
| lemma/substitution.v | Substitution Lemma for process and expression variables |
| lemma/decidable_helper.v | Helper functions relating to participant decidability |
| lemma/decidable.v | Lemmas regarding participant decidability |
| lemma/expr.v | Lemmas regarding expression evaluation |
| lemma/part.v | Lemmas regarding participants on subtrees |
| lemma/step.v | Lemmas regarding well-formedness of global trees after taking a step |
| lemma/projection_helper.v | Helper functions for projection related lemmas |
| lemma/projection.v | Lemmas regarding projections after global trees take a step | 
| lemma/main_helper.v | Helper functions for main theorems |
| lemma/main.v | Main Theorems |
