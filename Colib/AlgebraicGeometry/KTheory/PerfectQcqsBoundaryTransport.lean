/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectQcqsConnectiveLocalization
public import Colib.AlgebraicGeometry.KTheory.PerfectOrdinaryQcqsCofinality

/-! # Transporting naturality to the fine connective boundary

The genuine relative boundary and the proved positive comparison determine
naturality for fine perfect K-theory; no comparison at degree zero is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen

namespace AlgebraicGeometry.Scheme.Modules

universe u d e

variable {U X V Y : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ Y)
  [IsOpenImmersion j] [IsOpenImmersion k]
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace V]
  [HasDerivedCategory.{d} U.Modules] [HasDerivedCategory.{e} V.Modules]

/-- Commutativity of the relative boundary and the relative-to-fine comparison
implies commutativity of the original fine connective boundary. -/
theorem perfectQcqsConnectingHom_natural_of_relative (n : ℕ)
    (s : PerfectSupportedK j n →* PerfectSupportedK k n)
    (r : PerfectOpenK j (n + 1) →*
      PerfectOpenK k (n + 1))
    (t : (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace).K (n + 1) →*
      (RingedSpace.perfectComplexesWaldhausen V.toRingedSpace).K (n + 1))
    (hs : s.comp (perfectOpenConnectingHom j n) =
      (perfectOpenConnectingHom k n).comp r)
    (ht : t.comp (perfectOpenKRestrict j (n + 1)) =
      (perfectOpenKRestrict k (n + 1)).comp r) :
    s.comp (perfectQcqsConnectingHom j n) = (perfectQcqsConnectingHom k n).comp t := by
  have he := qcqs_perfectOpenKRestrict_succ_bijective j n
  ext x
  obtain ⟨a, rfl⟩ := he.surjective x
  have hj := DFunLike.congr_fun (perfectQcqsConnectingHom_comp_relative j n) a
  have hk := DFunLike.congr_fun (perfectQcqsConnectingHom_comp_relative k n) (r a)
  have hrs := DFunLike.congr_fun hs a
  have hrt := DFunLike.congr_fun ht a
  simp only [MonoidHom.comp_apply] at hj hk hrs hrt ⊢
  rw [hj, hrt, hk]
  exact hrs

end AlgebraicGeometry.Scheme.Modules
