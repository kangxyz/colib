/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectSupportedTransformationCone
public import Colib.AlgebraicGeometry.Modules.PerfectSupportedRestriction
public import Colib.Algebra.Homology.MappingCone.NaturalIso

/-! # Restricting a signed supported cone -/

@[expose] public noncomputable section

open CategoryTheory CochainComplex AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X V : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T : X.Opens)
local notation "P" => RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
local notation "Q" => RingedSpace.IsPerfectComplex (X := V.toRingedSpace)
local notation "R" => Functor.mapHomologicalComplex (restrictFunctor j) (ComplexShape.up ℤ)
local notation "Res" => perfectComplexesRestrictOpenImmersion j
local notation "Perf" => ObjectProperty.FullSubcategory P



variable (r : Γ(V, ⊤)) (q : (Γ((j ⁻¹ᵁ T).toScheme, ⊤))ˣ)
variable (hq : (j ⁻¹ᵁ T).ι.appTop r = ↑q)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- The full subcategory comparison unfolds both native restrict functors.
/-- A chart trivialization carrying a global coordinate to a scalar identifies the original
restricted cone functor with that scalar cone functor, on every perfect coefficient. -/
def perfectSupportedConeRestrictScalarIso
    {F G : Perf ⥤ Perf} (α : NatTrans F G)
    (hα : ∀ K : Perf, (perfectOpenWeakWaldhausen T.ι).weq (NatTrans.app α K))
    (i : F ⋙ Res ≅ Res) (k : G ⋙ Res ≅ Res)
    (h : Functor.whiskerRight α Res ≫ k.hom =
      i.hom ≫ Functor.whiskerLeft Res (perfectGlobalScalar V r)) :
    @Iso (Perf ⥤ (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory) _
      ((@perfectSupportedTransformationCone X T.toScheme T.ι inferInstance F G α hα) ⋙
        perfectSupportedRestrict j T)
      (Res ⋙ perfectSupportedScalarConeFunctor (j ⁻¹ᵁ T).ι r q hq) := by
  apply Functor.fullyFaithfulCancelRight (perfectSupported (j ⁻¹ᵁ T).ι).ι
  let J : X.Modules ⥤ V.Modules := restrictFunctor j
  let : J.Additive := inferInstanceAs ((restrictFunctor j).Additive)
  let IX := ObjectProperty.ι P
  let IY := ObjectProperty.ι Q
  let α₀ := Functor.whiskerRight α IX
  let β := Functor.whiskerLeft Res (perfectGlobalScalar V r)
  let β₀ := Functor.whiskerRight β IY
  let i' : (F ⋙ IX) ⋙ J.mapHomologicalComplex (ComplexShape.up ℤ) ≅ Res ⋙ IY :=
    Functor.isoWhiskerRight i IY
  let k' : (G ⋙ IX) ⋙ J.mapHomologicalComplex (ComplexShape.up ℤ) ≅ Res ⋙ IY :=
    Functor.isoWhiskerRight k IY
  have h' : Functor.whiskerRight α₀ (J.mapHomologicalComplex (ComplexShape.up ℤ)) ≫
      k'.hom = i'.hom ≫ β₀ := by
    apply NatTrans.ext
    funext K
    change IY.map ((Functor.whiskerRight α Res ≫ k.hom).app K) =
      IY.map ((i.hom ≫ β).app K)
    exact congrArg IY.map (NatTrans.congr_app h K)
  exact (mappingConeNatTransFunctorMapIso α₀ J).trans
    (mappingConeNatTransFunctorIso _ β₀ i' k' h')

end AlgebraicGeometry.Scheme.Modules
