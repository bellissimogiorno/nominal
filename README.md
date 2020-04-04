# nominal

## Basic information

The interaction of name-binding with structured datatypes can be tricky.  Examples include:

* Inductively defining syntax and reductions of a syntax with binding, e.g. lambda-calculus or System F.
* Graph-like structures, especially if they have danging pointers.

This package implements a nominal datatypes package in Haskell, based on names and swappings.  With it, you can define data with name-binding and program on this data in a nice manner that closely mirrors informal practice.  

The package design is based on a well-studied mathematical reference model as described in [a new approach to abstract syntax with variable binding](https://link.springer.com/article/10.1007/s001650200016) ([author's pdfs](http://www.gabbay.org.uk/papers.html#newaas-jv)).

For usage, please see: 

* [The tutorial](https://github.com/bellissimogiorno/nominal/blob/master/src/Language/Nominal/Examples/Tutorial.hs).  This covers the main points of the package, from the point of view of a working programmer wishing to see the functions in use.  It is best read directly from source code. 
* [An implementation of System F](https://github.com/bellissimogiorno/nominal/blob/master/src/Language/Nominal/Examples/SystemF.hs) is an illustrative example of those functions applied in something resembling typical practice.
* More examples are in preparation. 




## Acknowledgements

Thanks to Lars Brünjes for help and support. 
