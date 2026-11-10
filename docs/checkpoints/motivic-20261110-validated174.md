# Motivic validated checkpoint: 174 contribution sources

This checkpoint adds nine fully scoped native-validated sources to checkpoint `bed55e0d143b4a263a92f527faa28aaefac6468f`. The prior 165 source bytes are unchanged. Its historical 150-source main baseline `581293ea17843e6028d1a87aa055e55d918f9698` passed complete CI. This new increment deliberately skips CI and does not claim a fresh aggregate root build.

## New results

- Signed shift: the actual component sign (-1)^(q*r), differential and naturality, specialized to ordinary algebraic singular chains and canonical sheafification. Two production files, two actual consumers, 14 examples and 58 native declarations including generated declarations.
- Exterior finite push-pull: the actual incidence pushforward square and finite push-pull comparison with the common parameter diagonal. Two production files and an actual consumer, 69 native declarations.
- Geometrically integral pullback: the actual generic inverse-image and integral cycle pullback, with a real consumer. One production file and an actual consumer, 13 native declarations.

All nine sources compiled. Their five production owners passed all 15 native declaration linters and ordinary-axiom closure, and all nine exact sources passed textstyle. Source and output hashes match the saved native receipts. Their existing Colib dependencies match the frozen 165-source checkpoint; there are no additional unpublished Colib dependencies. The root adds exactly five production imports.

This is scoped acceptance of 140 new native declarations, not an independent mathematical review or a completed motivic migration. General signed exterior composition, its remaining stalk/Tor comparisons, transfer singular/sheaf-complex endpoints, genuine weight-one quasi-isomorphism and strict A1 invariance remain unfinished. The pending incidence stalk-pushout package is excluded because its upstream normalization is being rebuilt. The 174 contribution sources comprise 96 production files and 78 actual consumers; this count is not the repository size or a completion percentage.

Pins remain Lean 4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 and Stacks 5ed82d14634e8d9576bb844c7bd4e3da66d450e7. No kernel replay, new Library registration, or whole-project status claim is made. Prior checkpoint reports are unchanged.
