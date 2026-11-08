/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingExteriorFiberTensor

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open scoped TensorProduct

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (t : correspondenceIncidence f g h z w)

-- The full tensor model uses the actual image-fibre stalk and the actual residue-field action.
example (q : (correspondenceLeftImageExteriorProjection f g h i z w v).fiber
      ((correspondenceIncidenceMap f g h z w).toImage t)) :
    let K := (correspondenceIntermediateImage f g h z w).residueField
      ((correspondenceIncidenceMap f g h z w).toImage t)
    let L := (correspondenceIncidence f g h z w).residueField t
    let R := ((correspondenceLeftImageExteriorProjection f g h i z w v).fiber
      ((correspondenceIncidenceMap f g h z w).toImage t)).presheaf.stalk q
    letI := correspondenceRemainingImageFiberStalkAlgebra f g h i z w v t q
    letI : Algebra K L :=
      ((correspondenceIncidenceMap f g h z w).toImage.residueFieldMap t).hom.toAlgebra
    correspondenceRemainingExteriorFiberLocalModel f g h i z w v t q ≅
      Spec (.of (R ⊗[K] L)) :=
  correspondenceRemainingExteriorFiberTensorIso f g h i z w v t q

#check Stacks.Chow.correspondenceRemainingImageFiberStalkAlgebra
#check Stacks.Chow.correspondenceRemainingImageFiberStalkAlgebra_specMap
#check Stacks.Chow.correspondenceRemainingExteriorFiberLocalModel
#check Stacks.Chow.correspondenceRemainingExteriorFiberLocalModel_isPullback
#check Stacks.Chow.correspondenceRemainingExteriorFiberTensorIso
#check Stacks.Chow.correspondenceRemainingExteriorFiberTensorIso_inv_structure
#check Stacks.Chow.finsum_correspondenceRemainingExteriorFiberTensor_weight
