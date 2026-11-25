/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationStrictSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationStrictInput

open AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation

#check strictSourceNull
#check sourceLegConeSquare_apply
#check strictLaurentTrack_naturality
#check strictSeed
#check strictSeed_eq_wholeSeed

#check AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluationNull.originalNullComparison

#check seedHomotopy
#check seedHomotopy_apply

#check InputSeedWords.strict_seed_naturality
