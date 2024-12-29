# Artifact Submission Template

Title of the submitted paper: Formalising Subject Reduction and Progress for Multiparty Session Processes (Replication)
ECOOP submission number for the paper: 

## Metadata to provide during artifact submission in HotCRP
- The virtual machine was tested using VirtualBox 7.0.22 on a system running Ubuntu 22.04 LTS. 
- The host machine featured a 12th Gen Intel® Core™ i7-1255U (10-core) processor with 16 GiB of memory.
- Booting the VM image takes approximately 30 seconds, compiling the code requires around 2 minutes.
- There are no known compatibility issues with the container or VM environment.
- We claim all badges: functional, reusable, and available.
 
## Quick-start guide (Kick-the-tires phase)
### on the Host Machine
1. Download the `tsp.zip` image file.
2. Extract the contents to obtain `tsp.ova`. 
3. Install [VirtualBox](https://www.virtualbox.org/).
4. Open a terminal and type `virtualbox` (or double-click the icon if on Windows).
5. From the top menu, choose **File → Import Appliance** (this may take a minute or two).
6. After import, the VM named **tsp (type safety proof)** will appear under the "Tools" section.
7. Click on **tsp** and then the **Start** button in the top menu to boot the OS.
### on the Virtual Mahcine
8. On the login screen, select the **user** account, which has superuser rights.
9. Enter the password: `aa` to log in.

## Overview: What does the artifact comprise?
### Installed Software:
1. **opam** – Package manager for OCaml
2. **coqc 20.0** – Coq compiler
3. **coqide** – Integrated development environment for Coq
4. **ssreflect** – Coq library for formalized mathematics
5. **paco** – Coq library for implementing parametrized coinduction

### Contained Files:
1. **Coq Source Code** – Located in the `Desktop/proofs` directory
2. **Source Code Documentation** – Found in `Desktop/proofs/README` file

---

### Table:

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

---

## For authors claiming an available badge

We agree to publishing the artifact under a Creative Commons license.

## For authors claiming a functional or reusable badge
## Shell Instructions (on the Virtual Machine)

1. Open a terminal from the left menu bar.
2. Run: `cd Desktop/proofs` to navigate to the Coq source directory.
3. Run: `eval $(opam env)` to update the shell environment for Coq.
4. Run: `coq_makefile -f _CoqProject -o Makefile` to generate the Makefile.
5. Run: `make` to compile the library (this may take up to 2 minutes). A successful compilation indicates that all results hold.

---

## For authors claiming a reusable badge
## Exploring Proofs in CoqIDE (on the Virtual Machine)
- After the compilation is finished, you can open and explore the proof files using CoqIDE. 
- For instance, you can run `coqide process/subject_reduction.v` to open the `subject_reduction.v` file and step through the proofs interactively.

---

