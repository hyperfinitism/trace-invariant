# Trace invariant for combinatory logic

This repository contains supplementary materials for the paper [*Bluebirds and mockingbirds cannot produce a fixed-point combinator*](https://arxiv.org/abs/2609.21765).

It provides a Haskell library for computing trace invariants in combinator logic consisting of orthogonal, non-erasing reduction rules.
This includes the following built-in rules:

- `Bxyz => x(yz)`
- `Cxyz => xzy`
- `Ix => x`
- `Mx => xx`
- `Wxy => xyy`

as well as user-defined rules.
It also provides the `trace` and `invariant` commands.

## Trace and invariant

Fix a combinatory logic with orthogonal, non-erasing rules, a constant  that duplicates arguments (e.g. `M`, `S`, `W`), and a target variable.
`trace` follows the input term's leftmost-innermost (LI) reduction, keeping track of the pair `(q,p)` for each contraction of the target constant: `q` counts occurrences of the target variable in the duplicated argument, and `p` counts those strictly before the redex.

`--basis` selects built-in rules; `--rules FILE` adds custom rules, whose contractions can also be selected with `--track`.
`--variable` selects the variable (default `x`); input is `TERM` or `--term-file FILE`.
Limits are `--events` (default 20), `--steps` (default 10000 total contractions), and optional `--nodes`.

For a given term, its trace invariant is defined as its normal form, provided the term is normalisable; otherwise, it is defined as the infinite trace via tail equivalence.
Since normalisability and tail equivalence are generally undecidable, `trace` calculates only the requested prefix and terminates the calculation once it reaches normal form or hits a limit.

`invariant` returns the normal form if it is reached, or a periodic trace if a repeat is detected in the LI reduction.
If neither condition is met within the computational limit, it reports `unresolved`.
The periodic trace is a canonical repeating block representing the tail-equivalence class.

`invariant` supports only BMI/M and BWI/W via `--theory`.
Orthogonality and non-erasability alone do not guarantee that the trace of a non-normalisable term is infinite, nor that its tail-equivalence class is preserved by weak reduction.

## Build and install

Requires [GHC](https://github.com/ghc/ghc) 9.12 and [Cabal](https://github.com/haskell/cabal) 3.14.

```bash
cabal update
cabal build all
cabal test all --test-show-details=direct
```

To install the command-line tool:

```bash
cabal install exe:combinator-trace
```

## Examples

Compute traces from command line input:

```bash
# M-trace
cabal run combinator-trace -- trace --basis BMI --track M --events 6 'x(BM(B(BM)B)x)'

# W-trace
cabal run combinator-trace -- trace --basis BWI --track W --events 6 'B(WI)(BWB)x'
```

Compute traces from files:

```bash
# BM(B(BM)B)x
cabal run combinator-trace -- trace --basis BMI --track M --events 6 --term-file examples/ns-fpc.term
# x(BM(B(BM)B)x)
cabal run combinator-trace -- trace --basis BMI --track M --events 6 --term-file examples/ns-fpc-shifted.term

# B(WI)(BWB)x
cabal run combinator-trace -- trace --basis BWI --track W --events 6 --term-file examples/bwi-fpc.term
# x(B(WI)(BWB)x)
cabal run combinator-trace -- trace --basis BWI --track W --events 6 --term-file examples/bwi-fpc-shifted.term

# BM(CBM)x
cabal run combinator-trace -- trace --basis BCIM --track M --events 6 --term-file examples/bcm-fpc.term
# x(BM(CBM)x)
cabal run combinator-trace -- trace --basis BCIM --track M --events 6 --term-file examples/bcm-fpc-shifted.term
```

Compute traces with user-supplied rules:

```bash
# Yx, where Ya => a(Ya)
cabal run combinator-trace -- trace --rules examples/custom-y.json --track Y --events 6 --term-file examples/y-fpc.term

# B(SII)(CB(SII))x, where Sabc => ac(bc)
cabal run combinator-trace -- trace --rules examples/custom-s.json --track S --events 6 --term-file examples/bcis-fpc.term
```

Compute trace sequences and trace invariants:

```sh
# M(Ix)
cabal run combinator-trace -- trace --basis BMI --track M --events 6 --term-file examples/normalising.term
cabal run combinator-trace -- invariant --theory BMI --term-file examples/normalising.term

# x(x(MM))
cabal run combinator-trace -- trace --basis BMI --track M --events 6 --term-file examples/periodic.term
cabal run combinator-trace -- invariant --theory BMI --term-file examples/periodic.term
```

## How to cite

```bibtex
@misc{imamura2026bluebirdsmockingbirdsproducefixedpoint,
      title={Bluebirds and mockingbirds cannot produce a fixed-point combinator},
      author={Takuma Imamura},
      year={2026},
      eprint={2609.21765},
      archivePrefix={arXiv},
      primaryClass={math.LO},
      url={https://arxiv.org/abs/2609.21765},
}
```
