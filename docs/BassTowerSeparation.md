# T1 separation of actual finite strict Bass towers

COL-0354 supplies the missing point-set hypothesis for COL-0350 on the actual tower of
COL-0338. Both substantial quotient proofs retain the existing quotient relation and topology.

For the reduced mapping cone, the cylinder base fiber is exactly
`x = x₀ ∨ s = 1 ∨ (s = 0 ∧ f x = y₀)`. For the reduced double cylinder it is exactly
`x = A.point k ∨ (s = 0 ∧ f.map k x = B.point k) ∨
(s = 1 ∧ g.map k x = C.point k)`. Nonbase target fibers are full endpoint preimages;
valid interior fibers are singletons. Every branch is closed under precisely T1 input
hypotheses. No endpoint injectivity, target Hausdorff property or replacement model is used.

The five native owners follow reduced cone, reduced double cylinder, cone and parameter
looping, strict square, and finite strict diagram iteration. The last induction generalizes
over the entire initial diagram. Level zero and all independent cylinder, loop and structure
times are retained.

`ColibTest/BassTowerSeparation.lean` constructs the actual tower using
`strictDiagramTransition`, applies `Telescope.stableColimitIso` at arbitrary signed degree,
and checks its original inclusion equation at every stage and explicitly stage zero.
A row into the original strict small-Waldhausen category composes with its native prespectrum
functor, with original T1 proved rather than assumed. A supplied proved seed square feeds
`strictDiagramTransition_map` and the actual telescope comparison naturality theorem.
Concrete constant endpoint maps verify both double-cylinder endpoint base fibers and the
cone bottom base fiber for points distinct from the source basepoint.

The seed transformation and strict coefficient row remain inputs. This does not construct
the geometric Laurent seed or coefficient row, establish stable equivalence of iterated
maps, or claim point HEP, excision, nonbasepoint transport, Bass localization or TT 7.4.

Implementation reference: the two Separation files and ConeLoopSeparation, and only the T1
clauses of StrictSquareTopology and StrictDiagramTopology in original Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Quillen is proof reference, never an import.
