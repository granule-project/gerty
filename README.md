# Gerty

A minimal, dependently-typed programming language with graded types
based on Graded Modal Dependent Type Theory (grtt). You can find more
details about this type theory in our
[ESOP 2021 paper](https://arxiv.org/pdf/2010.13163.pdf).

The syntax is inspired by Agda (so please do check that great project
out) but extended with the notion of grading.

A simple example, but which capture the main ideas, is the polymorphic
identity function.  Without any grading information we can write
something that looks very much like what we might write in Agda;

	id : (a : Type 0) -> (x : a) -> a
	id = \a -> \x -> x

(to run this with gerty, save it to a file with .lam extension and then
run `gerty file.lam`).

Then we can add the full-grading information which captures how many
times each variable is used at both the type-level and the
computation-level:

    id : (a : (.0, .2) Type 0) -> (x : (.1, .0) a) -> a
	id = \a -> \x -> x

Grades are written in pairs where the first component is the
computation-level grading and the second component is the type-level
grading. Thus `(a : (.0, .2) Type 0) -> ...` is a dependent function
type where `a` is used `0` times computationally and `2` times in the
rest of the type.

You can see gerty's command line options by running `gerty --help`

	$ gerty --help
	----------------------------------------------------------------
	Gerty v0.1.0 - graded modal dependent type theory
	----------------------------------------------------------------

	  --help                                    Show information on flags
	  --version                                 Show version
	  --tyc-optimise                            Apply grade-directed optimisation to type checking
	  --benchmark                               Benchmarking: Timing on
	  --trials                                  Benchmarking: Number of times to repeat type checking
	  --silent                                  Run in silent mode
	  --info                                    Run in more verbose mode
	  --no-simplify-smt                         Don't simplify the SMT theorems
	  --simplify-smt                            Simplify the SMT theorems
	  --no-smt                                  Turn off SMT for type checking; use normalisation only
	  --use-smt                                 Turn on SMT for type checking
	  --debug                                   Run in debugging mode (mostly for devs)

## Install instructions

You will need [Z3 installed](https://github.com/Z3Prover/z3/releases).

Binary releases are currently available for MacOS only.

If you need a release for a different operation system then please open an issue and
we will try to get that to you as soon as we can.

To build gerty from source, make sure you have Stack on your system.

Now run

   git clone https://github.com/granule-project/gerty \
   && cd gerty \
   && stack setup \
   && stack install
   
This will instance the `gerty` binary for you.

# Development

## Directory structure

- `src` contains the majority of the source code for the project
- `tests/cases/legacy` contains old examples and tests which
  are incompatible with the current format of the language
  (but may be reintroduced if certain language features are
  added)
