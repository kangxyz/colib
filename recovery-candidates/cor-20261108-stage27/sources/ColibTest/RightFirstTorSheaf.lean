/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RightFirstTorSheaf

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open AlgebraicGeometry.TorFormula
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- Every Tor degree has its canonical incidence action before exterior pullback.
example [IsSeparated h]
    (q : correspondenceRightIntermediateSupportProduct f g h i z w v) (n : ℕ) :
    let π := correspondenceRightExteriorProjection f g h i z w v
    let P := (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q
    let P₀ := (correspondenceIncidence g h i w v).presheaf.stalk (π q)
    letI := correspondenceIncidenceTorModule g h i w v (π q) n
    letI : Algebra P₀ P := (π.stalkMap q).hom.toAlgebra
    stalkModuleCat (correspondenceRightIntermediateSupportProduct f g h i z w v)
        (correspondenceRightExteriorTorSheaf f g h i z w v n) q ≅
      ModuleCat.of P (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π q) n) :=
  correspondenceRightExteriorTorSheafStalkIso f g h i z w v q n

example [IsSeparated h]
    [IsLocallyNoetherian (correspondenceIntersectionAmbient g h i)] (n : ℕ) :
    (correspondenceRightExteriorTorSheaf f g h i z w v n).IsQuasicoherent ∧
      (correspondenceRightExteriorTorSheaf f g h i z w v n).IsFiniteType :=
  isQuasicoherent_isFiniteType_correspondenceRightExteriorTorSheaf f g h i z w v n

-- The full fibre length is retained without finiteness or reduction assumptions on the stalk.
example [IsSeparated h]
    [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)]
    (q : correspondenceRightIntermediateSupportProduct f g h i z w v) (n : ℕ) :
    let π := correspondenceRightExteriorProjection f g h i z w v
    let P := (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q
    let P₀ := (correspondenceIncidence g h i w v).presheaf.stalk (π q)
    letI := correspondenceIncidenceTorModule g h i w v (π q) n
    Module.length P ((correspondenceRightExteriorTorSheaf f g h i z w v n).presheaf.stalk q) =
      Module.length P₀ (correspondenceIncidenceAmbientTor g h i w v (π q) n) *
        Module.length P (P ⧸ (IsLocalRing.maximalIdeal P₀).map (π.stalkMap q).hom) :=
  length_correspondenceRightExteriorTorSheaf_eq_mul f g h i z w v q n

-- Arbitrary fields discharge base flatness, without making the first support flat over Y.
example (k : Type u) [Field k]
    (f' : X ⟶ Spec (.of k)) (g' : Y ⟶ Spec (.of k))
    (h' : Z ⟶ Spec (.of k)) (i' : W ⟶ Spec (.of k))
    (z' : pullback (C := Scheme) f' g') (w' : pullback (C := Scheme) g' h')
    (v' : pullback (C := Scheme) h' i') :
    Flat (correspondenceRightExteriorProjection f' g' h' i' z' w' v') := inferInstance
