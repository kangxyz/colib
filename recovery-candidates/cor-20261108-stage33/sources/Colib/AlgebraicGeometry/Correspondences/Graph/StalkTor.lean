/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.NormalIncidence
public import Colib.AlgebraicGeometry.Intersection.FlatSectionStalkTor

/-!
# Native local Tor for actual graph components

For every component of a normal locally Noetherian scheme, its actual graph
projection is open. Over a flat target, the ambient product projection is flat.
Those two geometric facts construct a flat ring section of the actual graph
component inclusion stalk map. The native Tor of that literal graph stalk and
an arbitrary scalar-extended support module has no positive degrees. Its degree
zero retains the actual ambient action and the full support-module length.

The source may be empty, disconnected or nonintegral. No global integral scheme,
componentwise nonemptiness, flat support module, or supplied ring comparison is
required. The component and all maps are the existing native ones.

Implementation source: `motivic_source_a6805c4`,
`Motivic/AlgebraicGeometry/Correspondences/Composition/Identity/Tor.lean`,
`isZero_incidenceTor_succ_componentIdentity_right` and its left analogue.
This reconstructs their local graph algebra input, not their full actual
incidence endpoint: identifying the other pulled-support stalk with the scalar
extension below remains a separate obligation. `Identity/Units.lean` finite-sum
assembly is not asserted. Native Stacks Tag 0357 supplies the open components.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  (φ : X ⟶ Y) (hφ : φ ≫ g = f) [IsSeparated g]
  [IsLocallyNoetherian X] [IsNormal X] (t : genericPoints X)

local notation "G" => (integralComponentAt (correspondenceGraphMap f g φ hφ t.val))

/-- The actual graph component supplies its own local scalar-extension map. -/
def graphComponentStalkExtension (c : (G).subscheme) :
    (G).subscheme.presheaf.stalk c →+* (pullback f g).presheaf.stalk ((G).subschemeι c) := by
  have := isOpenImmersion_integralComponentAt_graphMap_fst f g φ hφ t
  exact Scheme.Hom.openSectionStalkExtension (G).subschemeι (pullback.fst f g) c

/-- The literal graph inclusion stalk map retracts the constructed scalar extension. -/
@[simp]
theorem stalkMap_comp_graphComponentStalkExtension (c : (G).subscheme) :
    ((G).subschemeι.stalkMap c).hom.comp (graphComponentStalkExtension f g φ hφ t c) =
      RingHom.id ((G).subscheme.presheaf.stalk c) := by
  have := isOpenImmersion_integralComponentAt_graphMap_fst f g φ hφ t
  exact Scheme.Hom.stalkMap_comp_openSectionStalkExtension
    (G).subschemeι (pullback.fst f g) c

/-- Flatness is derived from the actual product projection and the clopen component. -/
theorem flat_graphComponentStalkExtension [Flat g] (c : (G).subscheme) :
    (graphComponentStalkExtension f g φ hφ t c).Flat := by
  have := isOpenImmersion_integralComponentAt_graphMap_fst f g φ hφ t
  exact Scheme.Hom.flat_openSectionStalkExtension (G).subschemeι (pullback.fst f g) c

/-- The actual graph stalk degree-zero Tor has exactly the support module's ambient action. -/
def graphComponentStalkTorZeroIso (c : (G).subscheme)
    (M : ModuleCat ((G).subscheme.presheaf.stalk c)) :
    (((Tor (ModuleCat ((pullback f g).presheaf.stalk ((G).subschemeι c))) 0).obj
      ((ModuleCat.restrictScalars ((G).subschemeι.stalkMap c).hom).obj
        (ModuleCat.of ((G).subscheme.presheaf.stalk c) ((G).subscheme.presheaf.stalk c)))).obj
      ((ModuleCat.extendScalars (graphComponentStalkExtension f g φ hφ t c)).obj M)) ≅
    (ModuleCat.restrictScalars ((G).subschemeι.stalkMap c).hom).obj M := by
  have := isOpenImmersion_integralComponentAt_graphMap_fst f g φ hφ t
  exact Scheme.Hom.openSectionStalkTorZeroIso (G).subschemeι (pullback.fst f g) c M

/-- Every actual graph-component local Tor has zero positive degrees over a flat target. -/
theorem isZero_graphComponentStalkTor_succ [Flat g] (c : (G).subscheme)
    (M : ModuleCat ((G).subscheme.presheaf.stalk c)) (n : ℕ) :
    IsZero (((Tor (ModuleCat ((pullback f g).presheaf.stalk ((G).subschemeι c))) (n + 1)).obj
      ((ModuleCat.restrictScalars ((G).subschemeι.stalkMap c).hom).obj
        (ModuleCat.of ((G).subscheme.presheaf.stalk c) ((G).subscheme.presheaf.stalk c)))).obj
      ((ModuleCat.extendScalars (graphComponentStalkExtension f g φ hφ t c)).obj M)) := by
  have := isOpenImmersion_integralComponentAt_graphMap_fst f g φ hφ t
  exact Scheme.Hom.isZero_openSectionStalkTor_succ (G).subschemeι (pullback.fst f g) c M n

/-- The support-first ordering also has zero positive Tor, using native Tor balancing. -/
theorem isZero_graphComponentStalkTor_succ_flip [Flat g] (c : (G).subscheme)
    (M : ModuleCat ((G).subscheme.presheaf.stalk c)) (n : ℕ) :
    IsZero (((Tor (ModuleCat ((pullback f g).presheaf.stalk ((G).subschemeι c))) (n + 1)).obj
      ((ModuleCat.extendScalars (graphComponentStalkExtension f g φ hφ t c)).obj M)).obj
      ((ModuleCat.restrictScalars ((G).subschemeι.stalkMap c).hom).obj
        (ModuleCat.of ((G).subscheme.presheaf.stalk c) ((G).subscheme.presheaf.stalk c)))) := by
  have := isOpenImmersion_integralComponentAt_graphMap_fst f g φ hφ t
  exact Scheme.Hom.isZero_openSectionStalkTor_succ_flip (G).subschemeι (pullback.fst f g) c M n

/-- Degree-zero graph-component Tor has the full local support-module length. -/
theorem length_graphComponentStalkTor_zero (c : (G).subscheme)
    (M : ModuleCat ((G).subscheme.presheaf.stalk c)) :
    Module.length ((pullback f g).presheaf.stalk ((G).subschemeι c))
      (((Tor (ModuleCat ((pullback f g).presheaf.stalk ((G).subschemeι c))) 0).obj
        ((ModuleCat.restrictScalars ((G).subschemeι.stalkMap c).hom).obj
          (ModuleCat.of ((G).subscheme.presheaf.stalk c) ((G).subscheme.presheaf.stalk c)))).obj
        ((ModuleCat.extendScalars (graphComponentStalkExtension f g φ hφ t c)).obj M)) =
      Module.length ((G).subscheme.presheaf.stalk c) M := by
  have := isOpenImmersion_integralComponentAt_graphMap_fst f g φ hφ t
  exact Scheme.Hom.length_openSectionStalkTor_zero (G).subschemeι (pullback.fst f g) c M

end Stacks.Chow
