# Supercompiler for Programs in a Model Language (Subset of Scala)

Supercompilation is a type of metacomputation that enables automatic analysis, optimization, specialization, and transformation of programs. For this, the program is executed in a generalized form, across a whole set of input data. During the supercompilation process, a computation tree is built, where the nodes represent parameterized states of the computation process — configurations. Using various heuristics, the tree is reduced to a final graph, from which the residual program is then condensed.

A distinctive feature of this supercompiler is the presence of a new method for analyzing the output formats of configurations, based on the formulation and subsequent refinement of format hypotheses.

## More About the Supercompiler
`paper.pdf`

## Before Running

Before running the supercompiler, the following steps need to be completed:

1. Install the Graphviz utility.
2. Install the required modules using pip:

```sh
pip install graphviz
pip install PyPDF2
pip install pyparsing
```

## Запуск

```sh
python supercompiler.py path_to_scala_file [--debug]
```

## Example Programs

Example programs can be found in the `tests/` folder.
