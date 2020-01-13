# Coq'Art

[![Travis][travis-shield]][travis-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Gitter][gitter-shield]][gitter-link]
[![DOI][doi-shield]][doi-link]

[travis-shield]: https://travis-ci.com/coq-community/coq-art.svg?branch=master
[travis-link]: https://travis-ci.com/coq-community/coq-art/builds

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[gitter-shield]: https://img.shields.io/badge/chat-on%20gitter-%23c1272d.svg
[gitter-link]: https://gitter.im/coq-community/Lobby


[doi-shield]: https://zenodo.org/badge/DOI/10.1007/978-3-662-07964-5.svg
[doi-link]: https://doi.org/10.1007/978-3-662-07964-5

Coq'Art is the familiar name for the first book on the Coq proof assistant
and its underlying theory, the Calculus of Inductive Constructions.
This project contains the source of all examples and the solution to 170
out of over 200 exercises from the book.

## Meta

- Author(s):
  - Yves Bertot (initial)
  - Pierre Castéran (initial)
- Coq-community maintainer(s):
  - Yves Bertot ([**@ybertot**](https://github.com/ybertot))
  - Pierre Castéran ([**@Casteran**](https://github.com/Casteran))
- License: [CeCILL-B](LICENSE)
- Compatible Coq versions: 8.10
- Additional Coq dependencies: none
- Coq namespace: `coqart`
- Related publication(s):
  - [Interactive Theorem Proving and Program Development](http://www.labri.fr/perso/casteran/CoqArt/) doi:[10.1007/978-3-662-07964-5](https://doi.org/10.1007/978-3-662-07964-5)

## Building instructions

``` shell
git clone https://github.com/coq-community/coq-art
cd coq-art
make   # or make -j <number-of-cores-on-your-machine>
```

## Documentation

For more information, see the [book website][book-url]
and the [publisher's website][publisher-url].

The repository is structured as follows.

### Book chapters

1. [A Brief Presentation of Coq](ch1_overview)
2. [Gallina: Coq as a Programming Language](ch2_types_expressions)
3. [Propositions and Proofs](ch3_propositions_proofs)
4. [Dependent Product](ch4_dependent_product)
5. [Everyday Logic](ch5_everydays_logic)
6. [Inductive Data Structures](ch5_everydays_logic)
7. [Tactics and automation](ch5_everydays_logic)
8. [Inductive Predicates](ch8_inductive_predicates)
9. [Functions and their specification](ch9_function_specification)
10. [Extraction and imperative programming](ch10_extraction_and_imperative_programs)
11. [A Case Study: binary search trees](ch11_search_trees)
12. [The Module System](ch12_modules)
13. [Infinite Objects and Proofs](ch13_co_inductive_types)
14. [Foundations of Inductive Types](ch14_fundations_of_inductive_types)
15. [General Recursion](ch15_general_recursion)
16. [Proof by reflection](ch16_proof_by_reflection)

### Additional material

- [Tutorial on type classes](tutorial_type_classes)
- [Tutorial on inductive and coinductive types](tutorial_inductive_co_inductive_types)
- [More exercises](more_exercises)

[book-url]: http://www.labri.fr/perso/casteran/CoqArt/
[publisher-url]: https://www.springer.com/gp/book/9783540208549
