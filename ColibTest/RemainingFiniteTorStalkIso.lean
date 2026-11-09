/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteTorStalkIso

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Stacks.ModuleStalkSpecialization

universe u

noncomputable section

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [IsSeparated g] [IsSeparated h]
  [IsLocallyNoetherian (correspondenceIntersectionAmbient f g h)]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (x : correspondenceLeftImageIncidence f g h i z w v)
  (q : correspondenceRemainingFiniteModel f g h i z w v x)

local notation3 (prettyPrint := false) "E" => correspondenceRemainingFiniteModel f g h i z w v x
local notation3 (prettyPrint := false) "B" => correspondenceRemainingFiniteRing f g h i z w v x
local notation3 (prettyPrint := false) "F" => correspondenceRemainingFiniteTorSheaf f g h i z w v x
local notation3 (prettyPrint := false) "M" => correspondenceRemainingFiniteTorModule f g h i z w v x

-- The comparison is at an arbitrary actual point, not just a reduced generic point.
example (b : B) :
    let := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
    let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
    correspondenceRemainingFiniteStalkAlgEquiv f g h i z w v hz hw x q
      (algebraMap B (Localization.AtPrime p.asIdeal) b) =
        ((E).presheaf.germ ⊤ q trivial) b :=
  correspondenceRemainingFiniteStalkAlgEquiv_algebraMap f g h i z w v hz hw x q b

example (n : ℕ) (m : M n) :
    correspondenceRemainingFiniteTorStalkLinearEquiv f g h i z w v hz hw x q n
      (LocalizedModule.mk m 1) = (F n).presheaf.germ ⊤ q trivial m :=
  correspondenceRemainingFiniteTorStalkLinearEquiv_mk_one f g h i z w v hz hw x q n m

-- All degrees use the same actual coefficient localization and scalar transport.
example (n : ℕ) {r : ℕ} (s : Fin r → B) :
    letI := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
    letI : Algebra B ((E).presheaf.stalk q) :=
      ((E).presheaf.germ ⊤ q trivial).hom.toAlgebra
    let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
    let e := correspondenceRemainingFiniteStalkAlgEquiv f g h i z w v hz hw x q
    letI := stalkModule (F n) q
    letI : Module (Localization.AtPrime p.asIdeal) ((F n).presheaf.stalk q) :=
      Module.compHom _ e.toRingEquiv.toRingHom
    Koszul.seqComplexTensor (fun j => algebraMap B (Localization.AtPrime p.asIdeal) (s j))
        (ModuleCat.of (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl (M n))) ≅
      Koszul.seqComplexTensor (fun j => algebraMap B (Localization.AtPrime p.asIdeal) (s j))
        (ModuleCat.of (Localization.AtPrime p.asIdeal) ((F n).presheaf.stalk q)) :=
  correspondenceRemainingFiniteTorKoszulStalkIso f g h i z w v hz hw x q n s
