/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.TopoiBridge.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.PullbackPreservesFlatness

/-!
# Arbitrary pullback of short exact sequences with flat quotient

The geometric pullback is not assumed exact on all sheaves. Stacks 0G6R applies to the
actual flat quotient. The site presentation below is the presentation in the pinned native
`MixedDerivedTensorOnARingedSpace`, extracted here to avoid importing its tensor applications.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The opens-site presentation of the actual morphism of ringed spaces. -/
def modulePullbackSiteHom {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    RingedToposSiteHom (Stacks.ToposBridge.ringedTopos X)
      (Stacks.ToposBridge.ringedTopos Y) where
  u := Opens.map f.hom.base
  isContinuous := RingedSpaceModuleAdjunction.opensMap_isContinuous f
  fSharp := Stacks.ToposBridge.commRingStructureHom f

/-- The opens-site presentation is a genuine morphism of sites. -/
theorem modulePullbackSiteHom_isMorphismOfSites {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    (modulePullbackSiteHom f).u.IsMorphismOfSites (Stacks.ToposBridge.ringedTopos Y).J
      (Stacks.ToposBridge.ringedTopos X).J :=
  StacksZariskiSite.isMorphismOfSites_opensMap f.hom.base

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- Arbitrary scheme pullback preserves a short exact sequence with a flat quotient. -/
@[stacks 0G6R "Actual scheme module pullback with flat third term"]
theorem shortExact_pullback_of_flat_quotient {X Y : Scheme.{u}} (f : X ⟶ Y)
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat (O := Y.sheaf) S.X₃) :
    (S.map (pullback f)).ShortExact :=
  RingedToposSiteHom.pullbackPreservesShortExact
    (RingedSpace.modulePullbackSiteHom f.toLRSHom.toShHom)
    (RingedSpace.modulePullbackSiteHom_isMorphismOfSites f.toLRSHom.toShHom) S hS hflat

end AlgebraicGeometry.Scheme.Modules
