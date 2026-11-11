# Elaborating the complete DVR descent and original branch sum

The runs use Colib checkpoint `e0c254d0cc2353cb467292c4cf2ba053cf405760`,
Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` and Stacks
`5ed82d14634e8d9576bb844c7bd4e3da66d450e7`. The production proofs use the
original native Milnor groups, integral closures, completion maps, norms and
tame symbols. The compiler options and 200,000-heartbeat limits are fixed.

## Typed witnesses in complete descent

`DVRCompletePGroupDescent.lean` initially timed out at an injectivity proof
that simplified a concrete scalar tower. Run
`remote-f80f716623fd411ba28496f6cc020d0f` used the archive source with
SHA-256 `326b138d9e59c2bdc9a46873467199956cba5c94396c0719510da7f3e1a2cdc9`.
Replacing both simplifications with explicit `upper_map_apply` equality
chains moved the first reported timeout but did not complete the declaration
in `remote-0d8ce192bfa84c33a07a7e843160abf1`. The second source hash was
`a9f6286775feab9fd3700be246ca584ce488ef2d169bab6afd3a2218d46f141f`.

A scoped probe with SHA-256
`be7a9f0c2f590a47aace5c4a926b308025344244c6dbfb8dfe5d04de0e3e3fb5`
added theorem-local diagnostics and phase markers to the second candidate.
Run `remote-6951c1879a7047a08a3f3b701a83c095` reached the closure-tower
setup marker 13,145 ms after the body marker, at 87,798,309 raw
`IO.getNumHeartbeats` ticks. The uniformizer marker never appeared. The
profiler reported 12.4 seconds in typeclass inference. The reductions
repeatedly unfolded integral closures and subalgebra carriers. The markers
bound the measured phase without identifying a single reduction as its cause.

The repair moves injectivity of the literal closure map and extraction of a
positive ramification pair into small typed private helpers. The main proof
takes typed projections for the original uniformizers and ramification
witnesses. The proof still supplies every original equation and weight to
the native descent theorem. The repaired source SHA-256 is
`7cd2f80d87b04f2ef544d5df3a6b3357e1624412f22aafa8d5680eef84219992`.
Run `remote-2de121332c5c4631900ff5d3eecabdd3` compiled the producer in
17 seconds and its actual consumer in 5.5 seconds. The same run compiled the
downstream complete adjoining-root producer and consumer.

## A single additive map for the original branches

The native original-branch square in `Norm/DVR.lean` timed out in
`remote-e547e3f09bdc4db7803ba293d1144a9d`. The probe in
`remote-251b35c7a7144d8b9c32a58e6e5105fc` reached the completion comparison
but stopped before the combined tensor and finite-sum rewrites. The probe
hash was
`e70367da8c7dc73324e9d0e35696d33268549046ea0976fd86ad2f18f87f3833`.

Typing the tensor equivalence and the whole tensor norm equality isolated
the sum rewrites. This candidate, with source SHA-256
`2a869b286c6386b8e75e6a482d67bbc4da58ddfec75068301cc63234f119c61f`,
still timed out in `remote-9b448d8a828d451599b7b4940f641097`. The
corresponding probe had SHA-256
`f8a57c9c01a2dcafcc4dc3ac81a13970234c3e70bc195782a20e769d3fd42e96`.
In `remote-118be4d537ec446b91b6a66709811ba0`, the two `map_sum` rewrites
used 125,362,007 raw heartbeat ticks and 5,057 ms between their markers.
The coordinate equality then completed. Matching the remaining branch
comparison exceeded the declaration limit.

The final proof composes the native tame symbol with the inverse residue
transport as one typed additive map. It applies `map_sum` to the literal
branch terms once and uses `congrArg` to transport each branch coordinate
equality. This keeps the completion algebra and branch index fixed while
avoiding general rewrite matching over the finite sum. The source SHA-256 is
`7ead82a298c968c06cc707a17a4fb0d67911062f1d8f051394713b5dff9b38bb`.
Run `remote-30b69c2ff1354285b0ee9f60f6408892` compiled the production module
in 57 seconds and the full original-branch consumer in 6.8 seconds.

The times are per-run observations under the pinned inputs. The producer and
consumer successes identify the accepted scope of the two performance cases.
Each recorded batch continued into later modules after these successes.

```sh
lake build +Colib.RingTheory.KTheory.MilnorK.Norm.DVRCompletePGroupDescent \
  +ColibTest.MilnorDVRCompletePGroupDescent \
  +Colib.RingTheory.KTheory.MilnorK.Norm.DVR +ColibTest.MilnorOriginalDVRNorm
```

## Reverse dependencies of the prime mixed-span formula

During the arbitrary-field extension on Colib `5004c34`, adding the new
coefficient and mixed-span declarations directly to the old providers
invalidated the legacy auxiliary comparison. Its unchanged source
`AuxiliaryMixedBranchError` took 806 seconds in native run
`remote-29ebed9cee4a415fa4c2d6ae14ce3627`. That frontend exited zero.
The surrounding batch was closed after retaining its successful outputs.

The new formulas now live in `DVRPrimeUniformizerFinite` and
`DVRMixedPrime`, which import the byte-identical old providers. The
new complete prime proof uses these new leaves. Run
`remote-7b36c165f0c64006992b328e90d6ad9d` compiled both relocated
modules with the same dependency pins and proof budgets. This isolates
the arbitrary-residue generalization from the old reverse dependencies.

```sh
lake build +Colib.RingTheory.KTheory.MilnorK.Norm.DVRMixedPrime
```

## Tensor residue lengths and norm transport

The first combined localization length proof exceeded the 200,000-heartbeat
limit at `whnf` in `remote-2a0fae45201e41ff871f88c3c1c8709d`. The repair
isolates the flat local length identity from the construction of the
closed-fiber quotient equivalence. It identifies the actual contraction
map before converting the length expression. The resulting
`TensorResidueFactors` passed in
`remote-bc9b0327bad04ffabb59dbdf1a1e6d5c` in 7 seconds.

The combined weighted norm proof reached another `whnf` timeout in
`remote-8bb0246532134974ac267bf027f14b53`. Separating the simple
presentation, the tensor tower proof and the final factor formulas
moved compilation to three explicit type errors in
`remote-45d25786c93a4e3496aca771611e3a98`. The final repair selects
`IsLocalRing.ResidueField.algebra` from the actual coefficient fiber
and uses its `Algebra.toModule` on each residue field. This fixes the
coherence with the generic point sum, whose residue module comes from
that coefficient algebra. The actual tensor tower, both final
factor formulas and their weighted DVR consumer passed in
`remote-5660b8a041434d09902524e4e44751a9` at the same limit.

## The complete finite square with weighted residue branches

The conditional complete-finite probe with SHA-256
`ea361ed527dac1a5fec6b68c4f12d5033b310f2da42e91fb395bb4d55a3f45b9`
exceeded 200,000 heartbeats at `isDefEq` while rewriting a branch norm,
then at `whnf` in the enclosing declaration in
`remote-50d2cff4a985466abb1ebd5d40f313bd`.

The production proof fixes the residue and norm additive maps before
taking the sum. Typed helpers handle the comparison in one complete
branch and the annihilation after restriction. The weighted comparison
receives the family of actual subalgebra carriers explicitly. The
ramification coefficient is transported as a natural scalar by
`map_nsmul`.

With unchanged compiler limits, run
`remote-8d6e5341faa34f00ad634fe3b64b40c9` compiled
`DVRCompleteFinite` in 28 seconds, then `CompletionBranch` and
`DVR` in 12 and 55 seconds respectively. The complete producer,
with SHA-256
`cd21cc8359fe36e65fec706750d43f912a539ed75b99a9e3ff3a968f428ff7df`,
uses the actual weighted residue theorem and the unconditional
prime-power norm squares.

```sh
lake build +Colib.RingTheory.KTheory.MilnorK.Norm.DVRCompleteFinite \
  +Colib.RingTheory.KTheory.MilnorK.Norm.DVR
```
