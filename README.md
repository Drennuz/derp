OCaml implementation of parsing with derivatives

It is a work in progress. Right now it only returns yes/no for parsing, next step will be to build a syntax tree/forest. 

To build, run:

```
source build
```

To use the parser, you need to create a grammar first. An example can be found in the testing section at the bottom of the source file. `test_grammar` is a recursive grammar of continuous "0" or "1"s.

The main function to use is the `recognize` function, which takes in a list of string tokens and returns true/false as parsing results. 

```ocaml
> recognize ["0";"1";"0"] test_grammar
- : true

> recognize ["0";"2"] test_grammar
- : false
```

Variable-length tokens are supported.
