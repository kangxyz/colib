# Reduced telescopes of loop prespectra

[COL-0339](https://kangxyz.github.io/colib/tag/COL-0339/) constructs the reduced
sequential mapping telescope of the native `Topology.LoopPrespectrum` objects.
The mathematical owner is `Colib.Topology.Prespectrum.Telescope`, followed by
`Colib.Topology.Prespectrum.TelescopeHomotopy`.

## The chosen space and its maps

At level k, take the disjoint union of the cylinders I × E(i)(k). Identify the
upper face (i, 1, x) with (i + 1, 0, f(i)(x)), and identify every point on every
basepoint cylinder with the initial basepoint. `Telescope.Space` is the actual
Mathlib topological quotient by these generating relations, not a packaged
collection of presumed telescope properties.

`structurePiece` applies the original structure loop while retaining cylinder
height. `structurePiece_respects` proves compatibility with both relations.
The continuous `structureMap` is then obtained by quotient descent into the
actual path space. These constructions supply `prespectrum` and its based
structure-map law.

`inclusion` uses the lower face of a cylinder. The whole cylinder is the coherent
`inclusionHomotopy` from that inclusion to the next inclusion after the original
transition. `desc` descends actual coherent maps and their whole homotopies;
`inclusion_desc`, `desc_cylinder` and `hom_ext` identify its maps on the generators.
Strict stagewise maps induce `map`; `inclusion_map`, `map_id` and `map_comp` prove
the inclusion, identity and composition laws on the original cylinders.

For strictly compatible stage homotopies, `homotopyFamily` first descends into
the compact-open space of interval maps. Evaluation then constructs
`mapHomotopy`. This avoids assuming that a product with an arbitrary quotient
map is again a quotient map. `mapHomotopy_cylinder` and `mapHomotopy_at` retain
both the full cylinder formula and every time slice. Homotopy time, cylinder
height and structure-loop time are independent coordinates.

## Source correspondence and scope

The implementation adapts the following original files, retaining their actual
quotient models, universes, maps, formulas and assumptions:

- `Quillen/Topology/Prespectrum/Telescope.lean`, all constructions and statements.
- `Quillen/Topology/Prespectrum/TelescopeHomotopy.lean`, all constructions and statements.

Both locators refer to Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The source license and author attribution
are retained in the Lean headers. Their foundational objects now come from the
native Colib/Mathlib/Stacks dependency chain; no Quillen or Aglib adapter is imported.

The homotopy compatibility assumption is a condition on the supplied stage
homotopies. It is not automatic for arbitrary stagewise homotopy equivalences.
No Omega-prespectrum property, stable homotopy-group colimit, stable
parameter-loop commutation, cone/fiber excision, Bass localization, or
Thomason--Trobaugh Theorem 7.4 is asserted here.

## Concrete consumer

`ColibTest.PrespectrumTelescope` constructs the constant real-line prespectrum
with constant structure loops, its telescope projection, a doubling map and a
nonconstant scalar homotopy. The projection detects a nonbasepoint at stage
zero. The tests verify the entire cylinder formulas, inclusion naturality at
zero and successors, and independent homotopy/height parameters. General
structure-map tests retain an independent loop parameter, so this coordinate
is not silently identified with the cylinder or homotopy parameter.
