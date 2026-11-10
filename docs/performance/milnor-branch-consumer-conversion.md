# Conversion in expanded Milnor branch consumers

The checks use Colib checkpoint `e0c254d0cc2353cb467292c4cf2ba053cf405760`,
Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` and Stacks
`5ed82d14634e8d9576bb844c7bd4e3da66d450e7`. The consumers import the actual
production theorems. Their statements keep the original Milnor groups, norm
and residue maps, quotient carriers, weights and hypotheses.

## Nested scalar branch square

The recovered explicit-quotient candidate had SHA-256
`57c269800d395b62e904de61f572fd6eed7a22b85b7a02abe68b80cd846c6b18`.
The scoped native build reached the consumer frontend and exceeded the original
85-second cutoff in run `remote-f1aa30dd352542b4bc58f81e16951a2d`. It inferred
the original producer proof into `hbranch` and then used `exact hbranch`.

The accepted consumer keeps that inference and assigns the existing local
proof term to the main goal. Lean checks the resulting declaration during the
ordinary native build. The source SHA-256 is
`e694e89ab95a65774770a4a20e4842ac73e4378d38b872298f3f1840d28f979e`.
Run `remote-22984e89ba3740f383b162229c71605b` built the complete test in
6.6 seconds and closed the scoped Lake command in 17.3 seconds under the same
85-second cutoff.

## Tensor branch residues

The original `ColibTest.MilnorTensorBranchLinear` source had SHA-256
`fbde91365cf6dec59d6cd8f8bf8b435703cecb53b78f595c18016cc2a66b025e`.
Its producer had SHA-256
`0d92c9b8b9c368760423915838608baaa7279d714e41770c6a5c36cff8ec989b`.
The frontend was still active after ten minutes in
`remote-44208f50a1de44d3b1dbcc122491058c`. The runner retained the other
completed consumers.

In the first instrumented run, the command evaluation layer buffered
`IO.getStderr`, including flushes. The prefix probe used the underlying
stderr handle and completed the original local instance declarations in
`remote-a11d42fbbc134a3aac81baa1005c38e0`. A full-file probe reached the
fourth example and then reached the fifth example roughly 114 seconds later
in `remote-89dcf72b6fc1401891616ecb78e77f31`. Use append mode for direct
stderr markers when stderr is redirected to a regular log file. These
observations isolate expensive expanded examples. They do not separately
measure type formation, proof conversion or kernel checking.

Examples 4 through 7 now infer the same production proof into a local
hypothesis and assign that term. All eleven statement blocks are unchanged.
The source SHA-256 is
`3a67c2acb5ec872ead9c96a1d661c9e76f87032f2c85ef352e7348818c34bf1c`.
Run `remote-c69a6f3fceef4a6e8bece796ed1b5641` built the actual consumer
with a 12.8-second native frontend and exit zero. The existing resource and
proof limits apply throughout.

For a scoped reproduction, build the named consumers with the pinned
production artifacts and the original options.

```sh
lake build +ColibTest.MilnorNestedScalarBranchSquare +ColibTest.MilnorTensorBranchLinear
```

These timings describe individual runs. The successful builds are the evidence
for the complete consumer declarations at their recorded source hashes.
