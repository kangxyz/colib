/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectScalarConeWaldhausen

/-!
# Supported cones of natural transformations on perfect complexes

The cone is the literal signed Mathlib cone of the component maps. The same
construction applies to multiplication by a section of a line bundle and to
the scalar multiplication maps on its local trivializations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CochainComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

local notation "P" => RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
local notation "Perf" => ObjectProperty.FullSubcategory P

/-- A natural transformation which becomes a quasi-isomorphism on the open gives
an actual supported cone functor. -/
def perfectSupportedTransformationCone {F G : Perf ⥤ Perf} (α : F ⟶ G)
    (hα : ∀ K, (perfectOpenWeakWaldhausen j).weq (α.app K)) :
    Perf ⥤ (perfectSupported j).FullSubcategory :=
  ObjectProperty.lift (perfectSupported j)
    (mappingConeNatTransFunctor (Functor.whiskerRight α (ObjectProperty.ι P)))
    (fun K => perfectOpenWeak_mappingCone_supported j (α.app K) (hα K))

/-- The supported construction retains the original component mapping cone. -/
@[simp]
theorem perfectSupportedTransformationCone_obj {F G : Perf ⥤ Perf} (α : F ⟶ G)
    (hα : ∀ K, (perfectOpenWeakWaldhausen j).weq (α.app K)) (K : Perf) :
    ((perfectSupportedTransformationCone j α hα).obj K).obj =
      mappingCone (α.app K).hom := rfl

instance perfectSupportedTransformationCone_additive {F G : Perf ⥤ Perf}
    [F.Additive] [G.Additive] (α : F ⟶ G)
    (hα : ∀ K, (perfectOpenWeakWaldhausen j).weq (α.app K)) :
    (perfectSupportedTransformationCone j α hα).Additive := by
  constructor
  intro K L f g
  apply ObjectProperty.hom_ext
  let C := mappingConeNatTransFunctor (Functor.whiskerRight α (ObjectProperty.ι P))
  exact C.map_add (f := f) (g := g)

/-- Literal supported transformation cones preserve the ambient short exact sequences
as soon as both endpoint functors do. -/
theorem perfectSupportedTransformationCone_shortExact {F G : Perf ⥤ Perf}
    [F.Additive] [G.Additive] (α : F ⟶ G)
    (hα : ∀ K, (perfectOpenWeakWaldhausen j).weq (α.app K))
    (S : ShortComplex Perf)
    (hF : ((S.map F).map (ObjectProperty.ι P)).ShortExact)
    (hG : ((S.map G).map (ObjectProperty.ι P)).ShortExact) :
    ((S.map (perfectSupportedTransformationCone j α hα)).map
      (ObjectProperty.ι (perfectSupported j))).ShortExact :=
  mappingConeNatTransFunctor_shortExact
    (Functor.whiskerRight α (ObjectProperty.ι P)) S hF hG


/-- The actual cone functor is exact when the endpoint functors preserve short exact
sequences and weak equivalences. -/
theorem perfectSupportedTransformationCone_waldhausenExact {F G : Perf ⥤ Perf}
    [F.Additive] [G.Additive] (α : F ⟶ G)
    (hα : ∀ K, (perfectOpenWeakWaldhausen j).weq (α.app K))
    (hF : ∀ S : ShortComplex Perf, (S.map (ObjectProperty.ι P)).ShortExact →
      ((S.map F).map (ObjectProperty.ι P)).ShortExact)
    (hG : ∀ S : ShortComplex Perf, (S.map (ObjectProperty.ι P)).ShortExact →
      ((S.map G).map (ObjectProperty.ι P)).ShortExact)
    (hwF : ∀ {K L : Perf} (g : K ⟶ L), QuasiIso g.hom → QuasiIso (F.map g).hom)
    (hwG : ∀ {K L : Perf} (g : K ⟶ L), QuasiIso g.hom → QuasiIso (G.map g).hom) :
    IsExact (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq
      (perfectSupportedWaldhausen j).cof (perfectSupportedWaldhausen j).weq
      (perfectSupportedTransformationCone j α hα) := by
  let : (perfectSupportedTransformationCone j α hα).Additive :=
    perfectSupportedTransformationCone_additive j α hα
  exact RingedSpace.perfectComplexes_lift_isExact X.toRingedSpace _
    (perfectSupported_cofibrationClosed j) _
    (fun S hS => perfectSupportedTransformationCone_shortExact j α hα S (hF S hS) (hG S hS))
    (fun g hg => by
      let : QuasiIso g.hom := hg
      let : QuasiIso (F.map g).hom := hwF g hg
      let : QuasiIso (G.map g).hom := hwG g hg
      change QuasiIso (mappingCone.map (α.app _).hom (α.app _).hom
        (F.map g).hom (G.map g).hom (congrArg (fun f => f.hom) (α.naturality g).symm))
      exact mappingCone_map_quasiIso _ _ _ _ _)


end AlgebraicGeometry.Scheme.Modules
