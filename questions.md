# Questions

## About heuristics

### Context

- We are designing a statically typed language for specification of graph coloring problems that would undergo a transformation to a unit-disk graph to then be solved by an appropriate hardware
- A preliminary grammar for this language is in grammar.tex
- Some examples of ill-typed specifications that we want the type system to reject are in errors.tex
- We are particularly interested in **poly-time** transformations of graphs that preserve the chromatic number, such transformations are called "safe"
- For some transformations, we accept them as "almost safe" if they do not lower the chromatic number, and have a constant/slow growing bound its growth (i.e. chromatic number is allowed to increase by a small constant after the transformation)
- Since there is not general polynomial-time algorithm that would convert an arbitrary graph into a (not necessarily isomorphic) unit-disk graph with the same chromatic number, we are providing several heuristic transformations that might not always work, but we assume they are _usually_ safe (possibly under extra conditions)

### Technology Stack

- We plan to use C++ (or, maybe, Haskell) to implement most of the ideas, including the language, type checker, compiler/interpreter (for graphs)
- We will be using Bloqade.jl for running simulations on the compiled UDGs

### Questions/goals for heuristics

- We want to

  1. verify our heuristics (prove that they are poly-time and either safe, almost safe, or at least that they definitely do not lower the chromatic number)
  2. make preconditions on each heuristic precise (understand when exactly the heuristic is safe/almost safe, etc.)
  3. design a type system for user specifications that would enable static checks for such preconditions, and supporting chains of transformations
  4. understand if the order of transformations may affect safety in some cases
