# Section variables that depend on local notation

Lean 4.35.0 at `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` and Mathlib
at `56a005855ea17e0b0958f73ec801ae140b0a1679` reproduce a synthetic
placeholder in the stored type of a section variable. The following
file was checked with `lake env lean -DautoImplicit=false -DwarningAsError=true`
in the pinned Mathlib checkout.

```lean
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Comma.Over.Basic

@[expose] public section

open CategoryTheory AlgebraicGeometry
universe u

variable (k : Type u) [Field k]
local notation "S" => Spec (CommRingCat.of k)

#check (Over S)
variable (X : Over S)

set_option pp.sorrySource true in
#check X

example : X.left = X.left := rfl
```

The first check prints `Over (Spec ↧k)`. The second prints
`X : Over (Spec (sorry …))`, with the placeholder located in the
`variable` command. The example reports `declaration uses sorry`
and the process exits with status 1. Replacing the declaration by
`variable (X : Over (Spec (CommRingCat.of k)))` makes both types
print with `Spec ↧k` and the process exits with status 0.

## Checks on the original declarations

In the ordinary Zariski opens application, job
`da96221d805c48e4b289ef4b08c139aa` at
`1e14f90a51a157260ac16a4c1fbe6e9c761b30d6` reported synthetic
placeholders in the coefficient and local-vanishing declarations.
The source used `variable (X : SmoothSite S)` with the same notation
for the spectrum. With the base written explicitly and the diagnostic
option removed, `Cohomology.Opens.LocalZero` built in job
`5bd7b843ad862fdf96a51dd843916108` at
`5bd7b843ad862fdf96a51dd8439161082a7b9c9a`.
That job reached a separate kernel timeout in the final cohomology
isomorphism.

For the original normal-bundle chart, the first explicit-map repair
`49ab67f81267158340a6444e5e237dbc57731a1a` in job
`893c9d5ab0aa4591a694186fad6f2c3f` left the map names unknown at
their use sites. The chart's section variable types abbreviated
`SmoothSite (Spec (CommRingCat.of k))`. Spelling out the base in
those binders allowed `Gysin.OpenNaturality.ThomChart` to build in
job `87e9cd6373c34db1a52f926f6dca64b1` at
`f45a06a9617062dbd59a8e8d88885b18f6e51dc2`.
This builds the actual restriction and support maps and the equality
for the pulled-back chart class.

## Specializing the cohomology comparison

After the explicit site binder repair, the ordinary opens target in
`5bd7b843ad862fdf96a51dd843916108` reached a deterministic kernel
timeout in `zariskiCohomologyOnOpensIso` after 155 seconds in the
module. The topology, local-zero and generic restriction providers
built in that run. Moving the restriction isomorphism into a separate
definition over an arbitrary ordinary coefficient produced the same
kernel diagnostic in the composite after 188 seconds in the module
at `d02417b8b3576cdaa6ad6bd729451b9cdb9734c6`, job
`d02417b8b3576cdaa6ad6bd729451b9c`.

The successful version defines `cohomologyOnOpensOfIso` for an
ordinary coefficient and an isomorphism to an arbitrary cohomology
presheaf target. It forms the absolute Zariski-to-Nisnevich
isomorphism separately at the smooth-site type. The final declaration
specializes the generic composition, using a local heartbeat budget of
450000. The original restriction and change-of-topology maps are the
factors of that composition.

Native file check `0f21df0858285abc035dfe1a6bc6e984` at
`0f21df0858285abc035dfe1a6bc6e984a3b7f583` returned exit 0.
The `Cohomology.Opens` module took 279 seconds to build on that
revision. The final comparison changed both the term structure and
the local allowance, so these timings describe the respective
checks.
