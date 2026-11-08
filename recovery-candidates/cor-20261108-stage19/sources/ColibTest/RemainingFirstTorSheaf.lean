/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFirstTorSheaf

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open AlgebraicGeometry.TorFormula
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- Ordinary sheaf pullback realizes the original Tor action, without finite-map flatness.
example [IsSeparated g]
    (q : correspondenceLeftIntermediateSupportProduct f g h i z w v) (n : ℕ) :
    let π := correspondenceLeftExteriorProjection f g h i z w v
    let P := (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk q
    let P₀ := (correspondenceIncidence f g h z w).presheaf.stalk (π q)
    letI := correspondenceIncidenceTorModule f g h z w (π q) n
    letI : Algebra P₀ P := (π.stalkMap q).hom.toAlgebra
    stalkModuleCat (correspondenceLeftIntermediateSupportProduct f g h i z w v)
        (correspondenceLeftExteriorTorSheaf f g h i z w v n) q ≅
      ModuleCat.of P (P ⊗[P₀] correspondenceIncidenceAmbientTor f g h z w (π q) n) :=
  correspondenceLeftExteriorTorSheafStalkIso f g h i z w v q n

#check Stacks.Chow.correspondenceLeftExteriorTorSheafStalkIso
#check Stacks.Chow.correspondenceTripleIncidenceFirstKoszulIsoTorSheaf
#check Stacks.Chow.length_correspondenceTripleIncidenceFirstKoszul_eq_torSheaf
