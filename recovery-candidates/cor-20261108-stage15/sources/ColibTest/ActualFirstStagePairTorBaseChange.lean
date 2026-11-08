/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.FirstStagePairTorBaseChange

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence Stacks.Chow
open scoped TensorProduct

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (x : correspondenceLeftIntermediateSupportProduct f g h i z w v)

local notation3 "π" =>
  (pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
    (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h))
local notation3 "D₀" =>
  (correspondenceSupportProduct f g h z w).presheaf.stalk
    (correspondenceIncidenceToSupportProduct f g h z w (π x))
local notation3 "P₀" => (correspondenceIncidence f g h z w).presheaf.stalk (π x)
local notation3 "D" =>
  (correspondenceTripleSupportProduct f g h i z w v).presheaf.stalk
    (correspondenceLeftIntermediateToTripleSupport f g h i z w v x)
local notation3 "P" =>
  (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk x
local notation3 "φ" => correspondenceLeftExteriorSupportStalkMap f g h i z w v x
local notation3 "η₀" => ((correspondenceIncidenceToSupportProduct f g h z w).stalkMap (π x)).hom
local notation3 "η" => ((correspondenceLeftIntermediateToTripleSupport f g h i z w v).stalkMap x).hom
local notation3 "p₀" => correspondenceIncidenceAmbientInclusion f g h z w (π x)
local notation3 "R₀" => (pullback g g).presheaf.stalk (correspondenceMiddlePair f g h p₀)
local notation3 "β" => ((correspondenceMiddlePair f g h).stalkMap p₀).hom
local notation3 "ρ" => correspondenceIncidenceSupportStalkMap f g h z w (π x)

example
    [Flat f] [Flat h] [IsSeparated g]
    [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    {r : ℕ} (t : Fin r → R₀) (ht : IsRegular R₀ (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h p₀) = Ideal.span (Set.range t)) (n : ℕ) :
    letI := correspondenceIncidenceTorModule f g h z w (π x) n
    letI : Algebra P₀ P := ((π).stalkMap x).hom.toAlgebra
    letI : Algebra D P := (η).toAlgebra
    Nonempty (((Koszul.seqComplexTensor (fun j => φ (ρ (β (t j)))) D).homology n) ≃ₗ[D]
      (P ⊗[P₀] correspondenceIncidenceAmbientTor f g h z w (π x) n)) :=
  correspondenceLeftExterior_originalPairTor_baseChange f g h i z w v x t ht hkt n
