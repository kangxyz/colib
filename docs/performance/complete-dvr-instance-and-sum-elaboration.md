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
