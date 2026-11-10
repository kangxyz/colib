/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectSupport
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectApproximation
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.ReflexiveFactorization
public import Colib.AlgebraicGeometry.Modules.PerfectSupportedClosure

/-!
# Supported bounded-above-flat approximation

The actual inclusion into native supported perfect complexes has approximation on compact
schemes. Both the relative replacement and its admissible quotient stay acyclic on the open.
The source keeps its exact-category cofibrations; they are not arbitrary ambient monomorphisms.

Adapted from Quillen `BoundedFlat/SupportComparison.lean:50-99` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the existing native relative flat factorization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open AlgebraicGeometry.RingedSpace StrictlyPerfect HomologicalComplex

universe u
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Include supported bounded-above-flat complexes without changing their complexes or maps. -/
def boundedAboveFlatPerfectSupportedInclusion :
    (boundedAboveFlatPerfectSupported j).FullSubcategory ⥤
      (perfectSupported j).FullSubcategory :=
  ObjectProperty.ιOfLE (show boundedAboveFlatPerfectSupported j ≤ perfectSupported j
    from fun _ h => ⟨h.1.1, h.2⟩)

/-- The actual supported inclusion is exact into the native ambient-monomorphism target. -/
theorem boundedAboveFlatPerfectSupportedInclusion_isExact :
    IsExact (boundedAboveFlatPerfectSupportedWaldhausen j).cof
      (boundedAboveFlatPerfectSupportedWaldhausen j).weq
      (perfectSupportedWaldhausen j).cof (perfectSupportedWaldhausen j).weq
      (boundedAboveFlatPerfectSupportedInclusion j) where
  zero h := by
    apply IsZero.of_full_of_faithful_of_isZero (perfectSupported j).ι
    exact (complexSubcategory_inclusion_exact (boundedAboveFlatPerfectSupported j)).zero h
  cofibration f hf :=
    (complexSubcategory_inclusion_exact (boundedAboveFlatPerfectSupported j)).cofibration f hf
  weak _ hf := hf
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (perfectSupported j).ι
    exact (complexSubcategory_inclusion_exact (boundedAboveFlatPerfectSupported j)).pushout hi h

/-- The actual cone retains both bounded flatness and the specified open support. -/
theorem boundedAboveFlatPerfectSupported_mappingCone {K L : CochainComplex X.Modules ℤ}
    (hK : boundedAboveFlatPerfectSupported j K) (hL : boundedAboveFlatPerfectSupported j L)
    (f : K ⟶ L) : boundedAboveFlatPerfectSupported j (CochainComplex.mappingCone f) :=
  ⟨boundedAboveFlatPerfectComplex_mappingCone hK.1 hL.1 f,
    (perfectSupported_coneClosed j ⟨hK.1.1, hK.2⟩ ⟨hL.1.1, hL.2⟩ f).2⟩

/-- The shift needed by the actual identity-cone cylinder retains support and bounded flatness. -/
theorem boundedAboveFlatPerfectSupported_shift_one {K : CochainComplex X.Modules ℤ}
    (hK : boundedAboveFlatPerfectSupported j K) :
    boundedAboveFlatPerfectSupported j (K⟦(1 : ℤ)⟧) :=
  ⟨boundedAboveFlatPerfectComplex_shift hK.1 1,
    (perfectSupported_X₃_of_shortExact j (CochainComplex.mappingCone_triangle_shortExact (𝟙 K))
      ⟨hK.1.1, hK.2⟩
      (perfectSupported_coneClosed j ⟨hK.1.1, hK.2⟩ ⟨hK.1.1, hK.2⟩ (𝟙 K))).2⟩

/-- Genuine joint data from the original supported identity-cone cylinders. -/
def boundedAboveFlatPerfectSupportedJointData :
    RowFactorization.JointData
      (NestedWeakEquivalences.refl (boundedAboveFlatPerfectSupportedWaldhausen j)) :=
  complexJointDataOfNested (boundedAboveFlatPerfectSupported j)
    (fun hK hL f => boundedAboveFlatPerfectSupported_mappingCone j hK hL f)
    (fun _ hK => boundedAboveFlatPerfectSupported_shift_one j hK) _

/-- The original relative replacement and its admissible quotient retain the actual support.
Only compactness of the ambient scheme is needed; the open need not be compact. -/
@[colib_tag "COL-0382",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportComparison.lean:68-99"
    "adaptation"
    "Actual supported App2 replacement, supported admissible quotient and strict triangle"]
theorem boundedAboveFlatPerfectSupportedInclusion_approximation [CompactSpace X] :
    HasApproximationProperty (boundedAboveFlatPerfectSupportedWaldhausen j)
      (perfectSupportedWaldhausen j) (boundedAboveFlatPerfectSupportedInclusion j) where
  reflects _ h := h
  lift {K L} f := by
    let K' : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory :=
      ⟨K.obj, K.property.1⟩
    let L' : ObjectProperty.FullSubcategory (IsPerfectComplex (X := X.toRingedSpace)) :=
      ⟨L.obj, L.property.1⟩
    let f' : (boundedAboveFlatPerfectInclusion X.toRingedSpace).obj K' ⟶ L' :=
      ObjectProperty.homMk f.hom
    obtain ⟨M, i, p, hi, hp, hfac⟩ :=
      (boundedAboveFlatPerfectInclusion_approximation X.toRingedSpace).lift f'
    have hpq : QuasiIso (show M.obj ⟶ L.obj from p.hom) := hp
    have hM : perfectSupported j M.obj :=
      (@perfectSupported_iff_of_quasiIso _ _ j _ M.obj L.obj p.hom hpq).2 L.property
    obtain ⟨Q, hQ, q, w, hS⟩ :=
      (boundedAboveFlatPerfectWaldhausen_cof_iff X.toRingedSpace i).1 hi
    have hQa : perfectSupported j Q :=
      perfectSupported_X₃_of_shortExact j hS ⟨K.property.1.1, K.property.2⟩ hM
    let M' : (boundedAboveFlatPerfectSupported j).FullSubcategory :=
      ⟨M.obj, M.property, hM.2⟩
    let i' : K ⟶ M' := ObjectProperty.homMk i.hom
    let p' : (boundedAboveFlatPerfectSupportedInclusion j).obj M' ⟶ L :=
      ObjectProperty.homMk p.hom
    refine ⟨M', i', p', ?_, hp, ?_⟩
    · exact (boundedAboveFlatPerfectSupportedWaldhausen_cof_iff j i').2
        ⟨Q, ⟨hQ, hQa.2⟩, q, w, hS⟩
    · apply ObjectProperty.hom_ext
      exact congrArg (fun s => s.hom) hfac

/-- Forget support while preserving the actual bounded-flat complex and morphism. -/
def boundedAboveFlatPerfectSupportedForget :
    (boundedAboveFlatPerfectSupported j).FullSubcategory ⥤
      (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory :=
  ObjectProperty.ιOfLE (show boundedAboveFlatPerfectSupported j ≤
    boundedAboveFlatPerfectComplex X.toRingedSpace from fun _ h => h.1)

/-- Forgetting support is exact for the actual bounded-flat exact structures. -/
theorem boundedAboveFlatPerfectSupportedForget_isExact :
    IsExact (boundedAboveFlatPerfectSupportedWaldhausen j).cof
      (boundedAboveFlatPerfectSupportedWaldhausen j).weq
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq
      (boundedAboveFlatPerfectSupportedForget j) where
  zero h := by
    apply IsZero.of_full_of_faithful_of_isZero (boundedAboveFlatPerfectComplex X.toRingedSpace).ι
    exact (complexSubcategory_inclusion_exact (boundedAboveFlatPerfectSupported j)).zero h
  cofibration f hf := by
    obtain ⟨Q, hQ, q, w, hS⟩ :=
      (boundedAboveFlatPerfectSupportedWaldhausen_cof_iff j f).1 hf
    exact (boundedAboveFlatPerfectWaldhausen_cof_iff X.toRingedSpace _).2
      ⟨Q, hQ.1, q, w, hS⟩
  weak _ hf := hf
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (boundedAboveFlatPerfectComplex X.toRingedSpace).ι
    exact (complexSubcategory_inclusion_exact (boundedAboveFlatPerfectSupported j)).pushout hi h

/-- The two actual inclusion routes are the same functor on complexes and chain maps. -/
theorem boundedAboveFlatPerfectSupportedInclusion_forget :
    (boundedAboveFlatPerfectSupportedInclusion j ⋙ perfectSupportedInclusion j :
      (boundedAboveFlatPerfectSupported j).FullSubcategory ⥤
        ObjectProperty.FullSubcategory (IsPerfectComplex (X := X.toRingedSpace))) =
      boundedAboveFlatPerfectSupportedForget j ⋙
        boundedAboveFlatPerfectInclusion X.toRingedSpace := rfl

end AlgebraicGeometry.Scheme.Modules
