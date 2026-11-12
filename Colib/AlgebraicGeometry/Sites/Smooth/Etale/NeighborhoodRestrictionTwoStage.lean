/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodInductionSmallStageAction

/-! # Restriction after the two actual fixed-clopen index refinements -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u v
namespace AlgebraicGeometry.Scheme.SmoothSite

theorem etaleNeighborhood_restriction_maps_eq_of_two_small_stages
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X T : SmoothSite S) [IsAffine X.left]
    (s : GeometricPoint X.left)
    {i₀ i : SmallEtaleNeighborhood X s} (e : i ⟶ i₀) (a : Over i)
    (ℓ : Over a.left) (Anew : EtaleNeighborhood X s.hom)
    (w : Anew ⟶ (smallEtaleNeighborhoodInclusion X s).obj ℓ.left)
    {D : Type v} [Category D] (Q : (SmoothSite S)ᵒᵖ ⥤ D) (f g : X ⟶ T)
    (hEq : Q.map (((etaleNeighborhoodToSmooth X s.hom).map w) ≫
        ((smallEtaleNeighborhoodToSmooth X s).map ℓ.hom ≫
          ((smallEtaleNeighborhoodToSmooth X s).map (a.hom ≫ e) ≫
            (etaleNeighborhoodHom X s.hom
              ((smallEtaleNeighborhoodInclusion X s).obj i₀) ≫ f)))).op =
      Q.map (((etaleNeighborhoodToSmooth X s.hom).map w) ≫
        ((smallEtaleNeighborhoodToSmooth X s).map ℓ.hom ≫
          ((smallEtaleNeighborhoodToSmooth X s).map (a.hom ≫ e) ≫
            (etaleNeighborhoodHom X s.hom
              ((smallEtaleNeighborhoodInclusion X s).obj i₀) ≫ g)))).op) :
    Q.map (etaleNeighborhoodHom X s.hom Anew ≫ f).op =
      Q.map (etaleNeighborhoodHom X s.hom Anew ≫ g).op := by
  let wS := (etaleNeighborhoodToSmooth X s.hom).map w
  let lS := (smallEtaleNeighborhoodToSmooth X s).map ℓ.hom
  let bSmall := (smallEtaleNeighborhoodToSmooth X s).map (a.hom ≫ e)
  let h₀ := etaleNeighborhoodHom X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i₀)
  have hb : bSmall ≫ h₀ =
      etaleNeighborhoodHom X s.hom ((smallEtaleNeighborhoodInclusion X s).obj a.left) :=
    etaleNeighborhoodMap_comp_hom (X := X) s.hom
      ((smallEtaleNeighborhoodInclusion X s).map (a.hom ≫ e))
  have hl : lS ≫ etaleNeighborhoodHom X s.hom
      ((smallEtaleNeighborhoodInclusion X s).obj a.left) =
      etaleNeighborhoodHom X s.hom ((smallEtaleNeighborhoodInclusion X s).obj ℓ.left) :=
    etaleNeighborhoodMap_comp_hom (X := X) s.hom
      ((smallEtaleNeighborhoodInclusion X s).map ℓ.hom)
  have hw : wS ≫ etaleNeighborhoodHom X s.hom
      ((smallEtaleNeighborhoodInclusion X s).obj ℓ.left) = etaleNeighborhoodHom X s.hom Anew :=
    etaleNeighborhoodMap_comp_hom (X := X) s.hom w
  have htotal : wS ≫ (lS ≫ (bSmall ≫ h₀)) = etaleNeighborhoodHom X s.hom Anew :=
    (congrArg (fun z => wS ≫ (lS ≫ z)) hb).trans
      ((congrArg (fun z => wS ≫ z) hl).trans hw)
  have normalize (z : X ⟶ T) :
      wS ≫ (lS ≫ (bSmall ≫ (h₀ ≫ z))) = etaleNeighborhoodHom X s.hom Anew ≫ z := by
    calc
      _ = (wS ≫ (lS ≫ (bSmall ≫ h₀))) ≫ z := by simp only [Category.assoc]
      _ = _ := congrArg (fun m => m ≫ z) htotal
  exact (congrArg (fun z => Q.map z.op) (normalize f)).symm.trans
    (hEq.trans (congrArg (fun z => Q.map z.op) (normalize g)))

end AlgebraicGeometry.Scheme.SmoothSite
