/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.FirstStageOriginalPairTor

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence Stacks.Chow
open scoped TensorProduct

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (x : correspondenceTripleIncidence f g h i z w v)

local notation3 "u" => correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x
local notation3 "π" =>
  (pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
    (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h))
local notation3 "p" => correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
local notation3 "p₀" => correspondenceIncidenceAmbientInclusion f g h z w (π u)
local notation3 "A" => correspondenceTripleIncidenceAmbientStalk f g h i z w v x
local notation3 "A₀" => correspondenceIncidenceAmbientStalk f g h z w (π u)
local notation3 "D" =>
  (correspondenceTripleSupportProduct f g h i z w v).presheaf.stalk
    (correspondenceTripleIncidenceToTripleSupport f g h i z w v x)
local notation3 "P" =>
  (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk u
local notation3 "P₀" => (correspondenceIncidence f g h z w).presheaf.stalk (π u)
local notation3 "R₀" => (pullback g g).presheaf.stalk (correspondenceMiddlePair f g h p₀)
local notation3 "β" => ((correspondenceMiddlePair f g h).stalkMap p₀).hom
local notation3 "α" => correspondenceTripleIncidencePairAmbientStalkMap f g h i z w v x
local notation3 "ε" => correspondenceTripleIncidenceSupportStalkMap f g h i z w v x
local notation3 "ρ" => correspondenceIncidenceSupportStalkMap f g h z w (π u)
local notation3 "φ" => correspondenceLeftExteriorSupportStalkMap f g h i z w v u
local notation3 "κ" => correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x
local notation3 "η" =>
  ((correspondenceLeftIntermediateToTripleSupport f g h i z w v).stalkMap u).hom
local notation3 "M" => correspondenceTripleIncidenceSupportStalkModule f g h i z w v x

example [IsSeparated g] :
    IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p =
      (RingHom.ker ((correspondenceTripleInclusion f g h).stalkMap
        (correspondenceIncidenceInclusion f g h z w (π u))).hom).map α :=
  correspondenceTripleIncidence_firstDiagonalIdeal_eq_map_pair f g h i z w v x

example
    [Flat f] [Flat h] [Flat i] [IsSeparated g]
    [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    {r : ℕ} (t : Fin r → R₀) (ht : IsRegular R₀ (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h p₀) = Ideal.span (Set.range t)) (n : ℕ) :
    let a := fun j => α (β (t j))
    let l := List.ofFn a
    let hreg := correspondenceOriginalPairList_first_regular f g h i z w v x t ht hkt
    letI := correspondenceTripleIncidenceFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    letI := correspondenceIncidenceTorModule f g h z w (π u) n
    letI : Algebra P₀ P := ((π).stalkMap u).hom.toAlgebra
    Nonempty ((Koszul.seqComplexTensor l.get M).homology n ≃ₗ[P]
      (P ⊗[P₀] correspondenceIncidenceAmbientTor f g h z w (π u) n)) :=
  ⟨correspondenceTripleIncidenceFirstKoszulIsoOriginalPairTor f g h i z w v x t ht hkt n⟩
