/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingExteriorFiberMap
public import Colib.RingTheory.Length.FieldExtensionBaseChange

/-!
# The actual fixed-label fibre model is the full residue-field tensor algebra

Fix an original incidence point `t` and a point `q` of the image exterior fibre
above its image. The full source exterior fibre, base changed to the spectrum
of the image-fibre stalk `R`, is canonically `Spec (R ⊗[κ(image t)] κ(t))`.
This follows by pasting the actual fibre square and applying native
`pullbackSpecIso`. The scalar map into `R` is recovered from the actual scheme
structure map by native `Spec.preimage`, and the comparison commutes with the
actual projection to `Spec R`.

At a generic image-fibre point the actual local ring is Artinian under local
Noetherianness of the full image exterior. The integer weighted branch formula
therefore applies to this actual tensor algebra: all maximal tensor branches
sum to the original residue degree times the full image-fibre multiplicity.
No separability, reduction, or multiplicity-one hypothesis is used. Reindexing
these maximal tensor primes as retained generic points of the original whole
exterior remains a separate step.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

local notation3 (prettyPrint := false) "pSource" =>
  correspondenceLeftExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "pImage" =>
  correspondenceLeftImageExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "originalMap" =>
  (correspondenceIncidenceMap f g h z w).toImage

variable (t : correspondenceIncidence f g h z w)

local notation3 (prettyPrint := false) "K₀" =>
  (correspondenceIntermediateImage f g h z w).residueField (originalMap t)
local notation3 (prettyPrint := false) "L₀" =>
  (correspondenceIncidence f g h z w).residueField t
local notation3 (prettyPrint := false) "Yₜ" => (pImage).fiber (originalMap t)
local notation3 (prettyPrint := false) "m" =>
  correspondenceRemainingExteriorFiberMap f g h i z w v t

section Point

variable (q : Yₜ)

local notation3 (prettyPrint := false) "R" => (Yₜ).presheaf.stalk q
local notation3 (prettyPrint := false) "sR" =>
  (Yₜ).fromSpecStalk q ≫ (pImage).fiberToSpecResidueField (originalMap t)

/-- The residue-field action on the actual image-fibre stalk, through its scheme structure map. -/
@[instance_reducible]
def correspondenceRemainingImageFiberStalkAlgebra : Algebra K₀ R :=
  (Spec.preimage sR).hom.toAlgebra

/-- The displayed stalk algebra induces exactly the actual composite scheme structure map. -/
theorem correspondenceRemainingImageFiberStalkAlgebra_specMap :
    letI := correspondenceRemainingImageFiberStalkAlgebra f g h i z w v t q
    Spec.map (CommRingCat.ofHom (algebraMap K₀ R)) = sR := by
  exact Spec.map_preimage sR

/-- The entire source exterior fibre localized over the actual image-fibre point. -/
abbrev correspondenceRemainingExteriorFiberLocalModel : Scheme.{u} :=
  pullback m ((Yₜ).fromSpecStalk q)

/-- The actual local fibre model is Cartesian over the two actual residue-field algebra maps. -/
theorem correspondenceRemainingExteriorFiberLocalModel_isPullback :
    letI := correspondenceRemainingImageFiberStalkAlgebra f g h i z w v t q
    letI : Algebra K₀ L₀ := ((originalMap).residueFieldMap t).hom.toAlgebra
    IsPullback (pullback.snd m ((Yₜ).fromSpecStalk q))
      (pullback.fst m ((Yₜ).fromSpecStalk q) ≫ (pSource).fiberToSpecResidueField t)
      (Spec.map (CommRingCat.ofHom (algebraMap K₀ R)))
      (Spec.map (CommRingCat.ofHom (algebraMap K₀ L₀))) := by
  let := correspondenceRemainingImageFiberStalkAlgebra f g h i z w v t q
  let : Algebra K₀ L₀ := ((originalMap).residueFieldMap t).hom.toAlgebra
  rw [correspondenceRemainingImageFiberStalkAlgebra_specMap]
  exact ((IsPullback.of_hasPullback m ((Yₜ).fromSpecStalk q)).paste_horiz
    (correspondenceRemainingExteriorFiberMap_isPullback f g h i z w v t).flip).flip

/-- A canonical scheme isomorphism to the spectrum of the full tensor algebra, not its reduction. -/
def correspondenceRemainingExteriorFiberTensorIso :
    letI := correspondenceRemainingImageFiberStalkAlgebra f g h i z w v t q
    letI : Algebra K₀ L₀ := ((originalMap).residueFieldMap t).hom.toAlgebra
    correspondenceRemainingExteriorFiberLocalModel f g h i z w v t q ≅
      Spec (.of (R ⊗[K₀] L₀)) := by
  let := correspondenceRemainingImageFiberStalkAlgebra f g h i z w v t q
  let : Algebra K₀ L₀ := ((originalMap).residueFieldMap t).hom.toAlgebra
  exact (correspondenceRemainingExteriorFiberLocalModel_isPullback
    f g h i z w v t q).isoPullback ≪≫ pullbackSpecIso K₀ R L₀

/-- The tensor comparison preserves the actual scalar projection to the image-fibre local ring. -/
theorem correspondenceRemainingExteriorFiberTensorIso_inv_structure :
    letI := correspondenceRemainingImageFiberStalkAlgebra f g h i z w v t q
    letI : Algebra K₀ L₀ := ((originalMap).residueFieldMap t).hom.toAlgebra
    (correspondenceRemainingExteriorFiberTensorIso f g h i z w v t q).inv ≫
        pullback.snd m ((Yₜ).fromSpecStalk q) =
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[K₀] L₀))) := by
  let := correspondenceRemainingImageFiberStalkAlgebra f g h i z w v t q
  let : Algebra K₀ L₀ := ((originalMap).residueFieldMap t).hom.toAlgebra
  change ((pullbackSpecIso K₀ R L₀).inv ≫
    (correspondenceRemainingExteriorFiberLocalModel_isPullback
      f g h i z w v t q).isoPullback.inv) ≫ _ = _
  rw [Category.assoc, IsPullback.isoPullback_inv_fst, pullbackSpecIso_inv_fst']

end Point

/-- At an actual generic image-fibre point, all tensor branches recover the original degree
multiplied by the full, possibly nonreduced, image-fibre multiplicity. -/
theorem finsum_correspondenceRemainingExteriorFiberTensor_weight [IsSeparated h]
    [IsLocallyNoetherian (correspondenceLeftIntermediateImageProduct f g h i z w v)]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (q : genericPoints Yₜ) :
    let R := (Yₜ).presheaf.stalk q.1
    letI := correspondenceRemainingImageFiberStalkAlgebra f g h i z w v t q.1
    letI : Algebra K₀ L₀ := ((originalMap).residueFieldMap t).hom.toAlgebra
    (∑ᶠ a : MaximalSpectrum (R ⊗[K₀] L₀),
      ((Module.length (Localization.AtPrime a.asIdeal)
        (Localization.AtPrime a.asIdeal)).toNat : ℤ) *
        (Module.finiteAlgebraResidueDegree R (R ⊗[K₀] L₀) a : ℤ)) =
      ((originalMap).residueDegree t : ℤ) * ((Module.length R R).toNat : ℤ) := by
  let R := (Yₜ).presheaf.stalk q.1
  let := correspondenceRemainingImageFiberStalkAlgebra f g h i z w v t q.1
  let : Algebra K₀ L₀ := ((originalMap).residueFieldMap t).hom.toAlgebra
  let := finite_correspondenceOriginalImageResidueField f g h z w hz hw t
  let : IsLocallyNoetherian Yₜ := isLocallyNoetherian_fiber pImage (originalMap t)
  let : IsArtinianRing R := generic_stalk_artinian q
  exact Module.finsum_natCast_length_mul_residueDegree_tensor_fieldExtension K₀ L₀ R

end Stacks.Chow
