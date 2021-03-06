# Isabelle/HoTT

An experimental implementation of [homotopy type theory](https://en.wikipedia.org/wiki/Homotopy_type_theory) in [Isabelle](https://isabelle.in.tum.de/).

### Usage

The default entry point for the logic is `HoTT`, import this to load everything else.

You can also load theories selectively, in this case, importing `HoTT_Base` is required and `HoTT_Methods` is helpful.

### What (and why) is this?

Isabelle/HoTT is a first attempt at bringing [homotopy type theory](https://en.wikipedia.org/wiki/Homotopy_type_theory) to the [Isabelle](https://isabelle.in.tum.de/) interactive theorem prover.
In its current state it is best viewed as a formalization of HoTT within Isabelle/Pure, largely following the development of the theory in the [Homotopy Type Theory book](https://homotopytypetheory.org/book/).

Work is slowly ongoing to develop the logic into a fully-featured framework in which one can formulate and prove mathematical statements, in the style of the univalent foundations school.
While Isabelle has provided support for object logics based on Martin-Löf type theory since the beginning, these have largely been ignored in favor of Isabelle/HOL.
Thus this project is also an experiment in creating a viable framework, based on dependent type theory, inside the simple type theoretic foundations of Isabelle/Pure.

### License

GNU LGPLv3
