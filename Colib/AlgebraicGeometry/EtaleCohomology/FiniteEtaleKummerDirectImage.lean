/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleKummerBoundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.InverseImage

/-!
# Trace of the Kummer sequence on the finite étale source

Transport the native trace through the genuine restriction comparison of Kummer
complexes. The extension-class compatibility does not assume a norm identification.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry
universe u w
namespace Stacks.EtaleCohomology
open Stacks.Kummer
variable {S Y : Scheme.{u}} (g : Y ⟶ S) [Etale g] [IsFinite g]

/-- The trace of the ACTUAL Kummer sequence on Y, not just restriction notation.
Transport is via the previously verified kernel comparison iso. -/
def finiteEtaleKummerTraceMorphism (n : ℕ) :
    (kummerSequence.{u, 0} Y n).map (etaleAbelianDirectImage.{u, 0} g) ⟶
      kummerSequence.{u, 0} S n :=
  (Functor.mapShortComplex (etaleAbelianDirectImage.{u, 0} g)).map
    (etaleRestrictionKummerIso g n).inv ≫ restrictedKummerTraceMorphism g n

/-- The coefficient trace on the actual mu_n sheaf of Y. -/
def finiteEtaleRootsOfUnityTrace (n : ℕ) :
    (etaleAbelianDirectImage.{u, 0} g).obj (rootsOfUnitySheaf.{u, 0} Y n) ⟶
      rootsOfUnitySheaf.{u, 0} S n :=
  (finiteEtaleKummerTraceMorphism g n).τ₁

/-- The third component is precisely the previously constructed Gm trace. -/
theorem finiteEtaleKummerTraceMorphism_τ₃ (n : ℕ) :
    (finiteEtaleKummerTraceMorphism g n).τ₃ =
      finiteEtaleMultiplicativeTrace g := rfl

variable [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- Ext-class compatibility for the genuine Kummer SES on Y. -/
theorem finiteEtaleKummerTrace_extClass {n : ℕ} (hn0 : n ≠ 0)
    (hS : IsUnit ((n : ℕ) : Γ(S, ⊤))) :
    ((kummerSequence_shortExact.{u, 0} Y hn0 (isUnit_natCast_of_hom g hS)).map_of_exact
      (etaleAbelianDirectImage.{u, 0} g)).extClass.comp
      (Ext.mk₀ (finiteEtaleRootsOfUnityTrace g n)) (add_zero 1) =
    (Ext.mk₀ (finiteEtaleMultiplicativeTrace g)).comp
      (kummerSequence_shortExact.{u, 0} S hn0 hS).extClass (zero_add 1) :=
  ShortComplex.ShortExact.extClass_naturality
    ((kummerSequence_shortExact.{u, 0} Y hn0 (isUnit_natCast_of_hom g hS)).map_of_exact
      (etaleAbelianDirectImage.{u, 0} g))
    (kummerSequence_shortExact.{u, 0} S hn0 hS)
    (finiteEtaleKummerTraceMorphism g n)

end Stacks.EtaleCohomology
end
