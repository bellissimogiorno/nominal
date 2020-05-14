# nominal

## Basic information

The interaction of name-binding and alpha-equivalence with data can be tricky.  Examples include:

* Inductively defining syntax and reductions of a syntax with binding, e.g. lambda-calculus or System F.
* Graph-like structures, especially if they have danging pointers.

This package implements a nominal datatypes package in Haskell, based on names and swappings.  With it, you can define data with name-binding and program on this data in a nice manner that closely mirrors informal practice. 
With it, you can define data with name-binding and program on this data in a manner closely mirroring informal practice.

The package design is based on a well-studied mathematical reference model as described in [a new approach to abstract syntax with variable binding](https://link.springer.com/article/10.1007/s001650200016) ([author's pdfs](http://www.gabbay.org.uk/papers.html#newaas-jv)).

For usage, please see: 

* [The tutorial](https://github.com/bellissimogiorno/nominal/blob/master/src/Language/Nominal/Examples/Tutorial.hs).  This covers the main points of the package, from the point of view of a working programmer wishing to see the functions in use.  
* [An implementation of System F](https://github.com/bellissimogiorno/nominal/blob/master/src/Language/Nominal/Examples/SystemF.hs) is an illustrative example of those functions applied in something resembling typical practice.
* [An implementation of a EUTxO blockchain system](https://github.com/bellissimogiorno/nominal/blob/master/src/Language/Nominal/Examples/IdealisedEUTxO.hs) is another, quite different, example of those functions applied in something resembling typical practice.
* More examples are in preparation. 


## Building and running

1. Install [Stack](https://github.com/commercialhaskell/stack).

2. Clone this repo:

        $ git clone https://github.com/bellissimogiorno/nominal.git
        $ cd nominal 

3. Build:

        $ stack build 

4. Read the documentation:

        $ stack haddock --open 

5. Run some unit- and property-based tests: 

        $ stack test 

5. Explore it in ghci:

        $ stack ghci Language/Nominal/Examples/SystemF.hs 
        $ stack ghci Language/Nominal/Examples/IdealisedEUTxO.hs 


## Acknowledgements

Thanks to Lars Brünjes for help, support, and code contributions. 
