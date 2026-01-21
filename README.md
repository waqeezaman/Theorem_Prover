# Theorem-Prover

A First-Order Logic (FOL) automated theorem prover written in **Haskell**. This tool implements the **Given Clause Algorithm** to determine the unsatisfiability of a set of axioms.


## Installation & Setup

### Prerequisites
* [GHC (Glasgow Haskell Compiler)](https://www.haskell.org/ghcup/) 9.4.8 or later.
* [Cabal](https://www.haskell.org/cabal/) build tool.

### Build
From the project root, run:
```bash
cabal update
cabal build
```

To add the prover to your PATH run: 
```bash 
cabal install --overwrite-policy=always
```

Then run 
```bash
Theorem-Prover
```

### Usage

```bash
Theorem-Prover <INPUT_FILE> [COMMAND] [FLAGS]
```

| Command | Description |
| :--- | :--- |
| `solve` | (Default) Runs the prover and outputs whether a contradiction was found. |
| `proof` | Extracts a linear proof and writes it to a file. |
| `nsteps` | Executes the search for a fixed number of iterations. |
| `search` | Exports the final Active and Passive clause sets to JSON. |

| Flag | Description |
| :--- | :--- |
| `-n, --steps INT` | Max iterations for the search (default: 3000). |
| `-o, --output FILE` | Path to save proof text or search JSON. |


### Examples

#### Standard solve (defaults to 'solve' command)
```bash
Theorem-Prover PUZ001-1.p
```

#### Save a proof to a file
```bash
Theorem-Prover PUZ001-1.p proof --output my_proof.txt
```

#### Export proof search state to JSON
```bash
Theorem-Prover PUZ001-1.p search --output search.json
```

#### Run for 500 steps specifically and export proof search to JSON
```bash
Theorem-Prover PUZ001-1.p nsteps -n 500 --output search.json
```

## Testing 

To run the tests run 

```bash 
cabal test 
```

Then consult the test logs to see the results.

## Evaluation 

Also included are a set of python scripts to evaluate the prover on sets of problems in the tptp format. 
Currently, there is no support for equality, and though there is code to convert problems to clausal form, the current prover assumes the problems are already in clausal form.

Consult the python scripts in `./evaluation` to evalaute the prover. 

## Todo 

**Create given clause loop that uses subsumption**
**Add support for equality - likely through superposition**
**Improve testing infrastructure** 
**Add full support for TPTP set, currently only works on cnf form, the code for transforming fof formulas already exists, but need to write parser for these types of problems**


## References
```bibtex
@inbook{Harrison_2009, 
  place={Cambridge}, 
  title={First-order logic}, 
  booktitle={Handbook of Practical Logic and Automated Reasoning}, 
  publisher={Cambridge University Press}, 
  author={Harrison, John}, 
  year={2009}, 
  pages={118–234}
}
```