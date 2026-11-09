# Strict-square cone-loop foundation (COL-0338)

## Source correspondence

Adapted from Quillen revision c561118b7795eb9780be9ed391c3251d6a4d0afd:

| Original owner | Native owner and retained result |
| --- | --- |
| Topology/Prespectrum/HomotopyPushout | Same path in Colib: quotient by the two ends and base cylinder; continuous loop structure; actual inclusions, coherent glue, descent, strict maps and identity/composition |
| Topology/Prespectrum/StrictSquareCone | Same path: iterated Arrow square, constant comparison track, strict comparison naturality and actual cone-loop functor |
| Topology/Prespectrum/StrictSquareNull | Same path: exact source leg, actual mapping-cone contraction and whole coherent null naturality with transported endpoints |
| Topology/Prespectrum/NullLoopNaturality | Same path: entire null/unit/null word naturality from all-time self-track and null equalities |
| Topology/Prespectrum/StrictSquareSeedNaturality | Same path: original scalar self-track seed and output-loop equality under its explicit scalar naturality input |
| KTheory/Bass/StrictDiagram | Same path: evaluation-square endofunctor, finite iterates, supplied-seed transition and stage-zero identification |
| KTheory/Bass/StrictDiagramMap | Same path: four-component map formula and finite-iterate transition naturality |

These are adaptations to native Topology.LoopPrespectrum and Mathlib category, Arrow,
continuous-map, Path and quotient objects. There are no Quillen or Aglib imports or adapters.
The generic construction does not require a Stacks import. Existing downstream scheme
objects retain the pinned Stacks dependency; it is not rebuilt or replaced here.

The quotient relation, topology and loop structure are constructed. Relation compatibility
uses the input prespectrum-map structure equations, not a new comparison hypothesis.
The cylinder and structure-loop parameters remain independent. The source null is the
literal mapping-cone contraction precomposed with the source leg. Whole null equality is
proved after explicit endpoint transport. No arbitrary null-compatibility field is added.

The scalar self-track and equality at every scalar time are genuine input to seed
naturality. The diagram endofunctor takes a strict evaluation-square functor Q. Its finite
transition takes a supplied natural transformation. Neither input is constructed for
schemes in this topic. Generic finite iteration is not a telescope or a proof of stable
Bass equivalence.

## Consumer

ColibTest.StrictSquareBass checks both quotient ends and the collapsed base cylinder,
continuity, independent cylinder/structure times, actual cone-loop functoriality, whole
source-null equality, its explicit level-zero specialization, scalar seed map and every
output-loop coordinate, diagram object identification, finite-iterate transition naturality
and the stage-zero seed. All signatures retain actual maps and source/target objects.

## Scope boundary

No scheme coefficient seed, geometric rectification, prespectrum telescope, nonconnective
identification, Bass supported localization or Thomason-Trobaugh 7.4 is asserted. In
particular this does not identify a support theory with the K-theory of a closed subscheme.
Author source comparison and local compilation are separate from independent review,
remote private axiom checks and publication.

## Constructed results versus inputs

| Constructed and proved here | Explicit generic input |
| --- | --- |
| Reduced double-cylinder quotient, continuous structure and coherent glue | Two actual prespectrum maps with their ordinary structure equations |
| Strict comparison and cone-loop functor, identity and composition | An object or morphism of Mathlib's iterated Arrow category |
| Canonical source contraction and whole null naturality | No extra null or null-naturality input |
| Exact null/unit/null seed map and its naturality | A scalar self-homotopy and equality of its full levels under the square map |
| Diagram endofunctor and finite iterates | A functor assigning a strictly natural evaluation square |
| Actual transition and all-stage transition naturality | A supplied seed natural transformation and its proved commuting square |

The last three inputs are interfaces for future applications, not declarations of newly
proved scheme geometry. Every construction field in the actual cylinder, prespectrum,
map, functor and nullhomotopy is filled by a definition or proof.
