"""Regression tests for Library ownership, permanent IDs and compiled reference integrity."""

from html import unescape
from pathlib import Path
import shutil
import json
import importlib.util
import re
import subprocess
import sys
import tempfile
import unittest

import catalog
import lean_code
import lint_style


class LibraryTests(unittest.TestCase):
    def assert_test_in_checks(self, module, check_path):
        self.assertIn(module, lint_style.source_modules(catalog.ROOT, "ColibTest"))
        self.assertIn("python3 scripts/lint_style.py", (catalog.ROOT / check_path).read_text())

    def setUp(self):
        self.library = catalog.load_library()
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        shutil.copytree(catalog.ROOT / "docs/library", self.root / "docs/library")
        shutil.copyfile(
            catalog.ROOT / "docs/references.toml", self.root / "docs/references.toml"
        )

    def test_k_theory_chapters_distinguish_general_ring_and_scheme_results(self):
        chapters = {chapter["id"]: chapter for chapter in self.library["chapters"]}
        self.assertEqual(chapters["k-theory"]["title"], "Algebraic K-Theory")
        self.assertEqual(chapters["k-theory-rings"]["title"], "Algebraic K-Theory of Rings")
        self.assertEqual(chapters["k-theory-schemes"]["title"], "Algebraic K-Theory of Schemes")
        self.assertIn("milnor-k-theory", chapters)
        order = [chapter["id"] for chapter in self.library["chapters"]]
        self.assertEqual(order[order.index("milnor-k-theory") + 1], "k-theory")
        self.assertNotIn("k-theory-rings-schemes", chapters)
        expected = {
            "COL-0001": ("k-theory", 'grothendieck-groups'),
            "COL-0338": ("k-theory", 'bass-delooping-diagrams-and-functoriality'),
            "COL-0004": ("k-theory-rings", "k-zero-of-fields"),
            "COL-0262": ("k-theory-rings", 'matsumoto-theorem'),
            "COL-0280": ("k-theory-rings", 'matsumoto-theorem'),
            "COL-0285": ("k-theory-schemes", 'vector-bundles-coherent-sheaves-and-comparison'),
            "COL-0255": ("milnor-k-theory", "milnor-degree-two"),
        }
        for identifier, (chapter, section) in expected.items():
            entry = self.library["entries"][identifier]
            self.assertEqual(entry["section"], section)
            self.assertEqual(self.library["sections"][section]["chapter"], chapter)
        matsumoto = self.library["entries"]["COL-0262"]
        self.assertIn("For every field", matsumoto["statement"])
        self.assertIn("Over a finite field", matsumoto["proof"])
        self.assertEqual(self.library["sections"]["matsumoto-theorem"]["entries"],
                         ["COL-0262", "COL-0280"])
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        self.assertEqual(set(built["entries"]), set(self.library["entries"]))

    def test_completion_milestone_native_scope_and_ci(self):
        root = catalog.ROOT
        ledger = json.loads((root / "docs/migration/milnor-completion.json").read_text())
        self.assertEqual(ledger["library_item"], "COL-0168")
        self.assertEqual(ledger["source_file"],
                         "Aglib/KTheory/MilnorK/Residue/AdicCompletion.lean")
        source = (root / "Colib/RingTheory/KTheory/MilnorK/Residue/Completion.lean").read_text()
        for declaration in ledger["source_declarations"].values():
            self.assertIn(declaration.removeprefix("Stacks.Chow."), source)
        self.assertIn("IsFractionRing.lift", source)
        self.assertIn("AdicCompletion.residueField_map_bijective", source)
        self.assertIn("dvrMilnorTameSymbol'_completion_eq_zero_iff", source)
        self.assertIn('colib_tag "COL-0168"', source)
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            self.assert_test_in_checks("ColibTest.MilnorCompletion", path)
        self.assertIn("Colib.RingTheory.KTheory.MilnorK.Residue.Completion",
                      (root / "Colib.lean").read_text())

    def test_import_all_keeps_native_dependency_boundary(self):
        source = self.root / "Colib" / "NativeImport.lean"
        source.parent.mkdir()
        for prefix in ("import", "public import", "meta import", "public meta import"):
            with self.subTest(prefix=prefix):
                source.write_text(f"module\n{prefix} all Mathlib.LinearAlgebra.TensorAlgebra.Basic\n")
                catalog.check_sources(self.root)

    def test_import_all_rejects_external_dependency(self):
        source = self.root / "Colib" / "ExternalImport.lean"
        source.parent.mkdir()
        for prefix in ("import", "public import", "meta import", "public meta import"):
            with self.subTest(prefix=prefix):
                source.write_text(f"module\n{prefix} all External.Module\n")
                with self.assertRaisesRegex(ValueError, "outside the dependency boundary"):
                    catalog.check_sources(self.root)

    def test_finite_coefficient_triangle_docstring_is_a_block_comment(self):
        relative = "Colib/Algebra/Homology/CochainComplex/FiniteCoefficients/Basic.lean"
        source = catalog.ROOT / relative
        self.assertIn(
            "/-- The canonical coefficient triangle `K --n--> K --> K/n --> K[1]`. -/",
            source.read_text(),
        )
        target = self.root / relative
        target.parent.mkdir(parents=True)
        shutil.copyfile(source, target)
        catalog.check_sources(self.root)

    def test_nested_block_comments_keep_dash_pairs_as_text(self):
        source = self.root / "Colib/NestedComments.lean"
        source.parent.mkdir()
        source.write_text(
            "/- outer -- still in the block /- inner -- axiom hidden -/ outer -/\n"
            "public import Mathlib.CategoryTheory.Category.Basic\n"
            "/-- A multiline block -- with /- nested\n"
            "native_decide -/ and a closing delimiter after --. -/\n"
        )
        catalog.check_sources(self.root)

    def test_real_line_comments_ignore_block_delimiters(self):
        source = self.root / "Colib/MixedComments.lean"
        source.parent.mkdir()
        source.write_text(
            "-- /- This does not open a block.\n"
            "/- A block -- not a line comment -/ -- -/ This does not close a block.\n"
            "public import Mathlib.CategoryTheory.Category.Basic\n"
            "-- /- An unterminated marker inside a final line comment."
        )
        catalog.check_sources(self.root)

    def test_unbalanced_block_comments_are_rejected(self):
        source = self.root / "Colib/UnbalancedComments.lean"
        source.parent.mkdir()
        for text in ("/- open", "/- outer /- inner -/", "-/", "-/ /-", "/- -- open\n"):
            with self.subTest(text=text):
                source.write_text(text)
                with self.assertRaisesRegex(ValueError, "Unbalanced comments"):
                    catalog.check_sources(self.root)

    def test_comments_do_not_hide_following_production_placeholders(self):
        source = self.root / "Colib/ForbiddenAfterComments.lean"
        source.parent.mkdir()
        for declaration in ("axiom forbidden : True", "theorem forbidden : True := by sorry"):
            with self.subTest(declaration=declaration):
                source.write_text(
                    "/- outer -- /- inner -/ outer -/\n-- ignored /-\n" + declaration
                )
                with self.assertRaisesRegex(ValueError, "Production placeholder or added axiom"):
                    catalog.check_sources(self.root)

    def test_comments_do_not_hide_following_external_imports(self):
        source = self.root / "Colib/ExternalAfterComments.lean"
        source.parent.mkdir()
        source.write_text("/- block -- text -/\n-- ignored /-\npublic import External.Module\n")
        with self.assertRaisesRegex(ValueError, "outside the dependency boundary"):
            catalog.check_sources(self.root)

    def test_independent_milestone_ids_keep_their_owners(self):
        expected = {
            "COL-0263": "milnor-symbols-field-change",
            "COL-0264": "milnor-symbols-field-change",
            "COL-0265": "koszul-coefficients",
            "COL-0266": "derived-hom-comparisons",
        }
        for identifier, section in expected.items():
            self.assertEqual(self.library["entries"][identifier]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in expected:
            self.assertTrue(result["entries"][identifier]["references"])

    def test_principal_euler_complete_chain_registration(self):
        root = catalog.ROOT
        leaves = ("Basic", "Additivity", "Support", "Filtration", "Associativity")
        for number, leaf in zip(range(169, 174), leaves):
            identifier = f"COL-{number:04d}"
            self.assertEqual(self.library["entries"][identifier]["section"], "principal-euler")
            module = f"Colib.RingTheory.Multiplicity.PrincipalEuler.{leaf}"
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            self.assert_test_in_checks("ColibTest.PrincipalEuler", path)
        source = (root / "Colib/RingTheory/Multiplicity/PrincipalEuler/Associativity.lean").read_text()
        self.assertIn("principalEuler_quotient_closedPoint_eq_zero", source)
        self.assertIn("principalCokernel_associativity", source)

    def test_finite_algebra_local_length_registration(self):
        root = catalog.ROOT
        for identifier, leaf in (("COL-0180", "FiniteAlgebraFiber"),
                                 ("COL-0181", "FiniteAlgebraLocal")):
            self.assertEqual(self.library["entries"][identifier]["section"],
                             "finite-algebra-coefficients")
            module = f"Colib.RingTheory.Length.{leaf}"
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            self.assert_test_in_checks("ColibTest.FiniteAlgebraLocal", path)
        self.assertIn("specialization", self.library["entries"]["COL-0181"]["scope"])

    def test_finite_algebra_norm_chain_registration(self):
        root = catalog.ROOT
        modules = {"COL-0182": "Colib.LinearAlgebra.Determinant.FiniteLength",
                   "COL-0183": "Colib.RingTheory.Norm.FiniteAlgebra",
                   "COL-0184": "Colib.RingTheory.Norm.PolynomialFiber"}
        for identifier, module in modules.items():
            self.assertEqual(self.library["entries"][identifier]["section"],
                             "finite-algebra-coefficients")
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            self.assert_test_in_checks("ColibTest.FiniteAlgebraNorm", path)

    def test_completion_branches_chain_registration(self):
        root = catalog.ROOT
        leaves = ("FiniteAlgebra", "ChineseRemainder", "SemilocalBranches",
                  "DedekindBranches", "FiniteDedekindBranches")
        for number, leaf in zip(range(185, 190), leaves):
            identifier = f"COL-{number:04d}"
            self.assertEqual(self.library["entries"][identifier]["section"], "adic-completion")
            module = f"Colib.RingTheory.AdicCompletion.{leaf}"
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            self.assert_test_in_checks("ColibTest.CompletionBranches", path)

    def test_fraction_residue_chain_registration(self):
        root = catalog.ROOT
        modules = {
            "COL-0190": "Colib.RingTheory.Localization.FiniteProductBaseChange",
            "COL-0191": "Colib.RingTheory.AdicCompletion.BranchFraction",
            "COL-0192": "Colib.RingTheory.AdicCompletion.FractionBranches",
            "COL-0193": "Colib.RingTheory.Norm.DVRResidue",
            "COL-0194": "Colib.RingTheory.Norm.DVRResidue",
        }
        for identifier, module in modules.items():
            section = ("adic-completion" if identifier < "COL-0193"
                       else "finite-algebra-coefficients")
            self.assertEqual(self.library["entries"][identifier]["section"], section)
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            for module in ("ColibTest.FractionBranches", "ColibTest.DVRResidueNorm"):
                self.assert_test_in_checks(module, path)

    def test_uniformizer_norm_complete_chain_registration(self):
        root = catalog.ROOT
        modules = {
            "COL-0195": "Colib.RingTheory.Henselian.UniformizerNormalization",
            "COL-0196": "Colib.RingTheory.DiscreteValuationRing.RamificationDegree",
            "COL-0197": "Colib.RingTheory.Norm.UniformizerBinomial",
            "COL-0198": "Colib.RingTheory.Norm.DVRUniformizer",
            "COL-0199": "Colib.RingTheory.Norm.DVRPrimeUniformizer",
        }
        for identifier, module in modules.items():
            section = ("henselian-ramification" if identifier < "COL-0197"
                       else "finite-algebra-coefficients")
            self.assertEqual(self.library["entries"][identifier]["section"], section)
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            for test in ("HenselianPrincipalRoots", "HenselianUniformizerNormalization",
                         "DVRRamificationDegree", "DVRUniformizerBinomial",
                         "DVRUniformizerNorm", "DVRPrimeUniformizerNorm"):
                self.assert_test_in_checks("ColibTest." + test, path)
        self.assertIn("ordinary norm-order", self.library["entries"]["COL-0199"]["scope"])

    def test_native_dvr_norm_order_registration(self):
        root = catalog.ROOT
        modules = {
            "COL-0200": "Colib.RingTheory.DiscreteValuationRing.FractionOrder",
            "COL-0201": "Colib.RingTheory.Norm.DVROrder",
        }
        for identifier, module in modules.items():
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            for test in ("DVRFractionOrder", "DVRNormOrder"):
                self.assert_test_in_checks("ColibTest." + test, path)
        source = (root / "Colib/RingTheory/Norm/DVROrder.lean").read_text()
        self.assertIn("theorem neg_log_valuation_norm", source)
        self.assertIn("theorem dvrFracOrd_norm_mk0", source)
        self.assertNotIn("[PerfectField", source)
        self.assertNotIn("[HenselianLocalRing", source)

    def test_charpoly_branch_complete_chain_registration(self):
        root = catalog.ROOT
        modules = {
            "COL-0202": "Colib.RingTheory.Charpoly.Basic",
            "COL-0203": "Colib.RingTheory.Charpoly.TensorProduct",
            "COL-0204": "Colib.RingTheory.Charpoly.DVRResidue",
            "COL-0205": "Colib.RingTheory.Charpoly.IntegralTensorProduct",
            "COL-0206": "Colib.RingTheory.Polynomial.PowerFactorCount",
            "COL-0207": "Colib.RingTheory.Charpoly.DVRBranchCount",
        }
        for identifier, module in modules.items():
            self.assertEqual(self.library["entries"][identifier]["section"],
                             "charpoly-branches")
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            for module in (
                    "ColibTest.FieldCharpolyPower",
                    "ColibTest.TensorCharpolyProduct",
                    "ColibTest.DVRCharpolyResidue",
                    "ColibTest.IntegralTensorCharpolyProduct",
                    "ColibTest.PolynomialPowerFactorCount",
                    "ColibTest.DVRCharpolyBranchCount",
            ):
                self.assert_test_in_checks(module, path)
        self.assertIn("infinite base field", self.library["entries"]["COL-0202"]["scope"])
        self.assertIn("power basis", self.library["entries"]["COL-0204"]["scope"])
        self.assertIn("Characteristic-zero", self.library["entries"]["COL-0207"]["scope"])

    def test_sylow_branch_native_chain_registration(self):
        root = catalog.ROOT
        modules = {
            "COL-0208": "Colib.FieldTheory.SylowFixedField",
            "COL-0209": "Colib.FieldTheory.AdjoinRootSplitBranchEmbedding",
            "COL-0210": "Colib.FieldTheory.PGroupNormalSubfield",
            "COL-0211": "Colib.FieldTheory.PGroupNormalSubfieldEmbedding",
        }
        for identifier, module in modules.items():
            self.assertEqual(self.library["entries"][identifier]["section"],
                             "sylow-field-reduction")
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
            self.assertNotIn("structure ", source)
            self.assertNotIn("def ", source)
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            for module in (
                    "ColibTest.SylowFixedField",
                    "ColibTest.AdjoinRootSplitBranchEmbedding",
                    "ColibTest.PGroupNormalSubfield",
                    "ColibTest.PGroupNormalSubfieldEmbedding",
            ):
                self.assert_test_in_checks(module, path)
        self.assertIn("Zero polynomials", self.library["entries"]["COL-0208"]["scope"])
        self.assertIn("No monicity", self.library["entries"]["COL-0209"]["scope"])
        self.assertIn("original field", self.library["entries"]["COL-0211"]["scope"])

    def test_additivity_keeps_actual_maps_scope_and_tests(self):
        expected = {
            "COL-0213": "geometric-realization",
            "COL-0214": "homotopy-colimits",
            "COL-0215": "homotopy-colimits",
            "COL-0216": "geometric-realization",
            "COL-0217": "homotopy-groups",
            "COL-0218": 'additivity-approximation-and-comparison-theorems',
            "COL-0219": 'additivity-approximation-and-comparison-theorems',
            "COL-0220": "geometric-realization",
            "COL-0212": 'waldhausen-k-theory',
        }
        for identifier, section in expected.items():
            self.assertEqual(self.library["entries"][identifier]["section"], section)
        self.assertIn("unreversed ordinal join", self.library["entries"]["COL-0216"]["scope"])
        self.assertIn("Infinite-dimensional", self.library["entries"]["COL-0216"]["scope"])
        self.assertIn("No comparison-equivalence or surjectivity assumption",
                      self.library["entries"]["COL-0219"]["scope"])
        self.assertIn("quotient-before-subobject", self.library["entries"]["COL-0219"]["scope"])
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in expected:
            self.assertTrue(result["entries"][identifier]["references"])
        ledger = json.loads((catalog.ROOT / "docs/migration/waldhausen/additivity.json").read_text())
        self.assertEqual(ledger["source_revision"], "c561118b7795eb9780be9ed391c3251d6a4d0afd")
        self.assertEqual(len(ledger["production_modules"]), 117)
        self.assertFalse((catalog.ROOT /
                          "Colib/CategoryTheory/Waldhausen/Additivity/NormalizeFunctor.lean").exists())
        self.assertIn("independent", self.library["entries"]["COL-0051"]["scope"])
        for test in ledger["tests"]:
            for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
                self.assert_test_in_checks(test, path)

    def test_ordinary_singular_topic_keeps_native_maps_and_scope(self):
        expected = {"COL-0347", "COL-0348", "COL-0349"}
        for identifier in expected:
            self.assertEqual(self.library["entries"][identifier]["section"],
                             "algebraic-simplices")
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        self.assertTrue(expected.issubset(result["entries"]))
        root = catalog.ROOT
        ledger = json.loads((root / "docs/migration/motivic-ordinary-singular-a1.json")
                            .read_text())
        self.assertEqual(len(ledger["modules"]), 13)
        imports = (root / "Colib.lean").read_text()
        for item in ledger["modules"]:
            self.assertIn("public import " + item["module"], imports)
            self.assertTrue((root / item["path"]).is_file())
        endpoint = (root / "Colib/AlgebraicGeometry/Simplex/HomotopyInvariance.lean").read_text()
        self.assertIn("ordinaryIntervalHomotopyEquiv", endpoint)
        self.assertIn("ordinaryIntervalHomologyIso", endpoint)
        self.assertIn('colib_tag "COL-0349"', endpoint)
        self.assertIn("No homotopy-invariance or transfer assumption",
                      self.library["entries"]["COL-0349"]["scope"])

    def test_dedekind_residue_endpoints_keep_original_scope(self):
        for identifier in ("COL-0603", "COL-0604", "COL-0605"):
            self.assertEqual(self.library["entries"][identifier]["section"],
                             "dedekind-residue-localization")
        self.assertIn("only in positive degrees", self.library["entries"]["COL-0603"]["scope"])
        self.assertIn("Generic G1 injectivity is an explicit hypothesis",
                      self.library["entries"]["COL-0604"]["scope"])
        self.assertIn("No generic G1 injectivity hypothesis or conclusion",
                      self.library["entries"]["COL-0605"]["scope"])

    def test_geometric_dedekind_topic_keeps_actual_maps_and_field(self):
        for identifier in ("COL-0611", "COL-0612", "COL-0613", "COL-0614"):
            self.assertEqual(self.library["entries"][identifier]["section"],
                             "coherent-g-theory-localization")
        self.assertIn("annihilated subcategory", self.library["entries"]["COL-0612"]["scope"])
        self.assertIn("supplied fraction field K", self.library["entries"]["COL-0613"]["scope"])
        self.assertIn("No generic G1 injectivity premise", self.library["entries"]["COL-0613"]["scope"])
        self.assertIn("degree-two statement", self.library["entries"]["COL-0614"]["scope"])

    def native_fixture(self):
        native = {
            "bindings": [],
            "citations": [],
            "stacks": [],
            "declarations": [],
            "modules": [],
        }
        module_names = {
            "coherent-g-theory-localization":
                "Colib.AlgebraicGeometry.KTheory.PrincipalClosedLocalization",
            "dedekind-residue-localization": "Colib.RingTheory.KTheory.GTheory.Dedekind.ResidueFieldAssembly",
            "resolution-devissage-and-serre-localization": "Colib.KTheory.Quillen.Basic",
            "additivity-approximation-and-comparison-theorems": "Colib.KTheory.Waldhausen.Basic",
            "waldhausen-fibration-and-boundary-maps": "Colib.KTheory.Waldhausen.Basic",
            "delooping-and-stable-localization": "Colib.KTheory.Waldhausen.Basic",
            "bass-delooping-normalization-and-telescopes": "Colib.KTheory.Bass.StrictDiagram",

            "bass-delooping-diagrams-and-functoriality":
                "Colib.RingTheory.KTheory.Bass.StrictLaurentSeedContraction",
            "finite-correspondences": "Colib.AlgebraicGeometry.Correspondences.Category",
            "transfers-nisnevich": "Colib.AlgebraicGeometry.SheavesWithTransfers.Sheafification",
            "transfer-homological-algebra": "Colib.AlgebraicGeometry.SheavesWithTransfers.EnoughInjectives",
            "reduced-transfer-tori": "Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorus",
            "exterior-parameters": "Colib.AlgebraicGeometry.Correspondences.Exterior.MixedIncidenceIso",
            "relative-principal-cuts":
                "Colib.AlgebraicGeometry.Correspondences.Cancellation.FiniteSupport.QuasiCompact",
            "transfer-singular-complexes": "Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Presheaf",
            "affine-line-invariance":
                "Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.PerfectField",
            "canonical-motivic-complexes": "Colib.AlgebraicGeometry.MotivicCohomology.Complex",
            "motivic-hypercohomology": "Colib.AlgebraicGeometry.MotivicCohomology.Hypercohomology",
            "weight-one-norm": "Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.QuasiIso",
            "weight-one-comparison": "Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.Hypercohomology",
            "diagonal-motivic-comparison": "Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.Corestriction",
            "sylow-field-reduction": "Colib.FieldTheory.PGroupNormalSubfieldEmbedding",
            "waldhausen-categories": "Colib.CategoryTheory.Waldhausen.Basic",
            "waldhausen-k-theory": "Colib.KTheory.Waldhausen.Basic",
            "bass-delooping-diagrams-and-functoriality": "Colib.KTheory.Bass.StrictDiagram",
            "homology-colimits": "Colib.Algebra.Category.ModuleCat.FilteredColimits",
            "affine-open-pairs": "Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.Functor",
            "scheme-products-and-index-squares":
                "Colib.AlgebraicGeometry.Scheme.PolynomialLaurentIndexSquare",
            "perfect-complexes": "Colib.AlgebraicGeometry.Modules.PerfectWaldhausen",
            "ext-scalars": "Colib.Algebra.Homology.DerivedCategory.Ext.Quotient",
            "ext-products": "Colib.Algebra.Homology.DerivedCategory.Ext.Bifunctor",
            "nisnevich-sites": "Colib.AlgebraicGeometry.Sites.Nisnevich.Basic",
            "algebraic-simplices": "Colib.RingTheory.AlgebraicSimplex.Basic",
            "projective-dimension": "Colib.RingTheory.Koszul.Ext",
            "koszul-coefficients": "Colib.RingTheory.Koszul.Coefficients",
            "derived-hom-comparisons": "Colib.Algebra.Homology.DerivedCategory.Ext.RightDerived",
            "finite-coefficient-composition":
                "Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.CompositionTriangle",
            "exact-categories": "Colib.CategoryTheory.ExactCategory.Basic",
            "bicategories": "Colib.CategoryTheory.Bicategory.IsoQuotient",
            "restricted-spans": "Colib.CategoryTheory.QConstruction.Basic",
            "tate-sphere-and-suspension": "Colib.AlgebraicGeometry.MotivicHomotopy.TateSphere",
            "eilenberg-mac-lane-representatives":
                "Colib.AlgebraicGeometry.MotivicHomotopy.EilenbergMacLane",
            "affine-line-representatives":
                "Colib.AlgebraicGeometry.MotivicHomotopy.AffineLineRepresentative",
            "reduced-cohomology-operations":
                "Colib.AlgebraicGeometry.MotivicHomotopy.ReducedMotivicBockstein",
            "pointed-simplicial-presheaves":
                "Colib.CategoryTheory.Sites.Simplicial.ReducedSuspensionCircle",
            "effective-motives":
                "Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Basic",
            "classifying-spaces": "Colib.Topology.ClassifyingSpace.Basic",
            "functor-constructions": "Colib.CategoryTheory.Functor.Rebase",
            "geometric-realization": "Colib.Analysis.Convex.StdSimplex.PathHomotopy",
            "homotopy-groups": "Colib.Topology.Homotopy.HomotopyGroup.Map",
            "homotopy-colimits": "Colib.Topology.Pushout.HomotopyEquivalence",
            "quillen-k-theory": "Colib.KTheory.Quillen.Basic",
            "grothendieck-groups": "Colib.KTheory.GrothendieckGroup.Basic",
            "k-zero-of-fields": "Colib.RingTheory.KTheory.GrothendieckGroup.Field",
            "quillen-k-theory-of-rings": "Colib.RingTheory.KTheory.Quillen.Field.FiniteFieldKTwo",
            "g-theory-of-rings": "Colib.RingTheory.KTheory.GTheory.FiniteModules.Localization",
            "vector-bundles-coherent-sheaves-and-comparison": "Colib.AlgebraicGeometry.KTheory.PerfectRestriction",
"support-and-connective-localization": "Colib.AlgebraicGeometry.KTheory.PerfectRestriction",
"units-tensor-products-and-localization-boundaries": "Colib.AlgebraicGeometry.KTheory.PerfectRestriction",
"support-and-connective-localization": "Colib.AlgebraicGeometry.KTheory.PerfectRestriction",
"thomason-trobaugh-localization": "Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterCurrentFullFiber",
"derived-pullback-and-flat-resolutions": "Colib.AlgebraicGeometry.KTheory.PerfectRestriction",
"affine-and-global-section-models": "Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSections",
"units-tensor-products-and-localization-boundaries": "Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorModelUnit",
"bass-k-theory-and-geometric-delooping": "Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorReturnedCell",
"affine-and-global-section-models": "Colib.AlgebraicGeometry.KTheory.PerfectRestriction",
"bass-k-theory-and-geometric-delooping": "Colib.AlgebraicGeometry.KTheory.PerfectRestriction",
            "matsumoto-theorem": "Colib.RingTheory.KTheory.MilnorK.QuillenEquivalence",
            "matsumoto-theorem": "Colib.RingTheory.KTheory.Quillen.Field.FiniteFieldKTwo",
            "milnor-symbols-field-change": "Colib.RingTheory.KTheory.MilnorK.Symbols.Basic",
            "milnor-residues-and-specialization": "Colib.RingTheory.KTheory.MilnorK.Residue.Specialization",
            "milnor-norms-and-rational-residues": "Colib.RingTheory.KTheory.MilnorK.Norm.DVRPrimeAnnihilation",
            "milnor-norms-on-curves": "Colib.RingTheory.KTheory.MilnorK.Norm.DVRComplete",
            "milnor-degree-two": "Colib.RingTheory.KTheory.MilnorK.Steinberg",
            "milnor-motivic-comparison": "Colib.AlgebraicGeometry.MotivicCohomology.WeightZero",
            "adic-completion": "Colib.RingTheory.AdicCompletion.FiniteAlgebra",
            "principal-euler": "Colib.RingTheory.Multiplicity.PrincipalEuler.Basic",
            "charpoly-branches": "Colib.RingTheory.Charpoly.DVRBranchCount",
            "henselian-ramification": "Colib.RingTheory.Henselian.UniformizerNormalization",
            "finite-algebra-coefficients": "Colib.RingTheory.Length.FiniteAlgebra",
        }
        item_modules = {
            "COL-0603": "Colib.RingTheory.KTheory.GTheory.Dedekind.ResidueFieldAssembly",
            "COL-0604": "Colib.RingTheory.KTheory.GTheory.Dedekind.Localization",
            "COL-0605": "Colib.RingTheory.KTheory.GTheory.Dedekind.FiniteResidue",
            "COL-0609": "Colib.RingTheory.KTheory.GTheory.Dedekind.LocalDvrBoundaryNaturality",
            "COL-0610": "Colib.RingTheory.KTheory.GTheory.Dedekind.LocalDvrBoundaryNaturality",
            "COL-0593":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedBassTelescope",
            "COL-0594":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenKZeroExact",
            "COL-0595":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenRestrictionStable",
            "COL-0596":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientFullOpenBassLocalization",
            "COL-0597":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterTelescopeNull",
            "COL-0598":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterCurrentFullFiber",
            "COL-0586":
                "Colib.KTheory.Bass.StrictDiagramIndexRowMapTelescopeNaturality",
            "COL-0587":
                "Colib.RingTheory.KTheory.Bass.StrictLaurentSeedContraction",
            "COL-0588":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFiberBassTelescope",
            "COL-0589":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenKZeroExact",
            "COL-0590":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFullOpenBassLocalization",
            "COL-0591":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterTelescopeComparison",
            "COL-0592":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryCurrentLocalization",
            "COL-0581":
                "Colib.KTheory.Bass.StrictDiagramCofiberDescent",
            "COL-0582":
                "Colib.AlgebraicGeometry.KTheory.Bass.GeometricChiPermutation",
            "COL-0583":
                "Colib.AlgebraicGeometry.KTheory.Bass.SchemeSeedRotation",
            "COL-0584":
                "Colib.AlgebraicGeometry.KTheory.Bass.SchemeIteratedSeedTelescope",
            "COL-0585":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterIteratedTwistedFiber",
            "COL-0576":
                "Colib.KTheory.Bass.StrictDiagramIndexRowTelescope",
            "COL-0577":
                "Colib.KTheory.Bass.ModelDiagramStableEquivalence",
            "COL-0578":
                "Colib.AlgebraicGeometry.Scheme.IntegerBaseSpecSquare",
            "COL-0579":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionTelescope",
            "COL-0580":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterFineTelescope",
            "COL-0571":
                "Colib.Topology.Prespectrum.StrictSquareConeInterchange",
            "COL-0572":
                "Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeSchemeNaturality",
            "COL-0573":
                "Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedTelescope",
            "COL-0574":
                "Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedNull",
            "COL-0575":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullTwistedFiberComparison",
            "COL-0564":
                "Colib.Topology.Prespectrum.ZigzagSequentializationColimit",
            "COL-0565":
                "Colib.KTheory.Bass.NormalizedStageMapStable",
            "COL-0566":
                "Colib.AlgebraicGeometry.KTheory.Bass.SchemeCurrentStageTelescopeStable",
            "COL-0567":
                "Colib.KTheory.Bass.NormalizedDiagramNull",
            "COL-0568":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullCurrentNull",
            "COL-0569":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryCurrentNull",
            "COL-0570":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullCurrentFiberComparison",
            "COL-0559":
                "Colib.CategoryTheory.Functor.IsoRouteTargetNormalization",
            "COL-0560":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalTensorNormalizedSupport",
            "COL-0561":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedCoefficientExact",
            "COL-0562":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedCoefficientSmallCylinder",
            "COL-0563":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorSupportedForgetRectangle",
            "COL-0556":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientKOne",
            "COL-0557":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatReturnedTensorGenerators",
            "COL-0558":
                "Colib.AlgebraicGeometry.KTheory.BoundedFlatReturnedTensorGeneratedTrace",
            "COL-0552":
                "Colib.KTheory.Bass.DiagramRowNormalizedBoundaryHomotopy",
            "COL-0553":
                "Colib.KTheory.Bass.ModelRowZigzagBackward",
            "COL-0554":
                "Colib.KTheory.Bass.WholeSeedWord",
            "COL-0555":
                "Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowCurrentBoundary",
            "COL-0548": "Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationEquivalence",
            "COL-0549": "Colib.Topology.Prespectrum.RowNormalizedOperation",
            "COL-0550": "Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorReturnedCell",
            "COL-0551": "Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorReturnedStrictification",
            "COL-0058": "Colib.Topology.ClassifyingSpace.NerveHomotopy",
            "COL-0098": "Colib.Analysis.Convex.StdSimplex.BoundaryRetraction",
            "COL-0388": "Colib.AlgebraicGeometry.Correspondences.Exterior.Graph",
            "COL-0402": "Colib.AlgebraicGeometry.Sites.Smooth.Units.UnitComplex",
            "COL-0403": "Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.SheafComparison",
            "COL-0404": "Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.Hypercohomology",
            "COL-1008": "Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.IntegralEquivalence",
            "COL-1007": "Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOne",
            "COL-1021": "Colib.RingTheory.KTheory.MilnorK.Norm.AcrossUniverses",
            "COL-1022": "Colib.RingTheory.KTheory.MilnorK.Norm.ChosenMixedTower",
            "COL-1024": "Colib.RingTheory.KTheory.MilnorK.Norm.DVRPurePrimeComplete",
            "COL-1026": "Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.MilnorEquivalence",
            "COL-1027": "Colib.RingTheory.KTheory.MilnorK.Norm.AcrossUniversesFinite",
            "COL-1030":
                "Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.HomotopyInvariance",
            "COL-1031": "Colib.AlgebraicGeometry.MotivicCohomology.CohomologySheafInvariance",
            "COL-1032":
                "Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteCohomologicalDimension",
            "COL-1033": "Colib.AlgebraicGeometry.MotivicCohomology.AffineLineInvariance",
            "COL-1039": "Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation",
            "COL-1041":
                "Colib.AlgebraicGeometry.Correspondences.Cancellation.PrincipalCutFaceGeometry",
            "COL-1043":
                "Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.Pencil.Weighted",
            "COL-1044":
                "Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedComparison.SingularEvaluation",
            "COL-1045":
                "Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.Suslin",
            "COL-1028":
                "Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.HomotopyInvariance",
        }
        native["modules"] = [
            {"name": name, "imports": []}
            for name in sorted(set(module_names.values()) | set(item_modules.values()))
        ]
        for identifier, entry in self.library["entries"].items():
            name = entry.get("primary", "CategoryTheory.example_" + identifier.removeprefix("COL-"))
            native["bindings"].append({"name": name, "id": identifier})
            native["declarations"].append(
                {
                    "name": name,
                    "type": "Prop",
                    "module": item_modules.get(identifier, module_names[
                        self.library["entries"][identifier]["section"]
                    ]),
                    "dependencies": [],
                }
            )
            native["citations"].append(
                {
                    "name": name,
                    "source": "stacks",
                    "locator": "fixture",
                    "relation": "comparison",
                    "scope": "Metadata-validation fixture",
                }
            )
        return native

    def test_exact_equivalence_keeps_canonical_maps(self):
        item = self.library["entries"]["COL-0179"]
        self.assertEqual(item["section"], "waldhausen-k-theory")
        self.assertIn("canonical K-theory maps", item["statement"])
        self.assertIn("strict chosen-zero preservation is not required", item["scope"])
        self.assertIn("No equality with archived named `PerfectK`", item["scope"])
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        self.assertTrue(result["entries"]["COL-0179"]["references"])

    def test_cor_transfer_reading_routes_keep_new_items(self):
        expected = {
            "finite-correspondences": (
                "cycles", [374, *range(363, 368)], ["COL-0374", "COL-0366"]
            ),
            "transfers-nisnevich": (
                "transfers", [*range(368, 374), 1028],
                ["COL-0368", "COL-0370", "COL-0372", "COL-1028"]
            ),
        }
        for section_id, (chapter, numbers, starts) in expected.items():
            section = self.library["sections"][section_id]
            self.assertEqual(section["chapter"], chapter)
            identifiers = [f"COL-{number:04d}" for number in numbers]
            self.assertEqual(section["entries"], identifiers)
            self.assertEqual([topic["start"] for topic in section["topics"]], starts)
            self.assertEqual(set(section["transitions"]), set(identifiers))
            for identifier in identifiers:
                item = self.library["entries"][identifier]
                self.assertTrue(item["primary"])
                self.assertEqual(item["path"], f"docs/library/entries/{chapter}/{identifier}.toml")

    def test_cycle_algebra_and_scheme_chapters_keep_distinct_owners(self):
        chapters = {chapter["id"]: chapter for chapter in self.library["chapters"]}
        self.assertEqual(chapters["cycles"]["sections"],
                         ["finite-correspondences", "exterior-parameters", "relative-principal-cuts"])
        self.assertEqual(chapters["transfers"]["title"], "Presheaves and Sheaves with Transfers")
        self.assertEqual(chapters["transfers"]["sections"],
                         ["transfers-nisnevich", "transfer-homological-algebra",
                          "transfer-singular-complexes", "affine-line-invariance"])
        self.assertLess(chapters["cycles"]["order"], chapters["transfers"]["order"])
        self.assertLess(chapters["transfers"]["order"], chapters["motivic-cohomology"]["order"])
        self.assertEqual(chapters["algebraic-geometry"]["sections"],
                         ["affine-open-pairs", "scheme-products-and-index-squares",
                          "perfect-complexes", "nisnevich-sites", "algebraic-simplices"])
        self.assertLess(chapters["algebraic-geometry"]["order"], chapters["cycles"]["order"])
        section = self.library["sections"]["finite-algebra-coefficients"]
        self.assertEqual(section["chapter"], "commutative-algebra")
        numbers = [10, 11, 12, 180, 181, 182, 183, 184, 193, 194, 197, 198, 199, 201]
        identifiers = [f"COL-{number:04d}" for number in numbers]
        self.assertEqual(section["entries"], identifiers)
        self.assertEqual([topic["start"] for topic in section["topics"]],
                         ["COL-0010", "COL-0182", "COL-0193", "COL-0197"])
        self.assertEqual(set(section["transitions"]), set(identifiers))
        for identifier in identifiers:
            self.assertEqual(self.library["entries"][identifier]["path"],
                             f"docs/library/entries/commutative-algebra/{identifier}.toml")
        self.assertEqual(self.library["entries"]["COL-0362"]["section"],
                         "bass-k-theory-and-geometric-delooping")

    def test_native_transfer_torus_exterior_items_keep_owners_and_scope(self):
        expected = {
            "transfer-homological-algebra": (
                "transfers", ["COL-0390", "COL-0381", "COL-0391", "COL-0392"]
            ),
            "transfer-singular-complexes": (
                "transfers", ["COL-0397", "COL-1030", "COL-1039", "COL-1045"]
            ),
            "affine-line-invariance": ("transfers", ["COL-1029"]),
            "reduced-transfer-tori": ("motivic-cohomology", ["COL-0384", "COL-0385"]),
            "exterior-parameters": ("cycles", ["COL-0386", "COL-0388", "COL-0387", "COL-0389"]),
            "relative-principal-cuts": ("cycles", ["COL-1040", "COL-1041", "COL-1043"]),
        }
        for section_id, (chapter, identifiers) in expected.items():
            section = self.library["sections"][section_id]
            self.assertEqual(section["chapter"], chapter)
            self.assertEqual(section["entries"], identifiers)
            self.assertEqual(set(section["transitions"]), set(identifiers))
            for identifier in identifiers:
                item = self.library["entries"][identifier]
                self.assertTrue(item["primary"])
                self.assertEqual(item["path"], f"docs/library/entries/{chapter}/{identifier}.toml")
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        output = self.render_site_fixture(built)
        for section_id in expected:
            page = (output / f"sections/{section_id}/index.html").read_text()
            self.assertIn('class="section-transition"', page)
            for identifier in expected[section_id][1]:
                self.assertTrue((output / f"tag/{identifier}/index.html").is_file())
        for identifier in ("COL-0397", "COL-1029"):
            page = (output / f"tag/{identifier}/index.html").read_text()
            self.assertIn('href="../../chapters/transfers/">Presheaves and Sheaves with Transfers</a>',
                          page)
        quotient = self.library["entries"]["COL-0390"]
        self.assertIn("surjective", quotient["statement"])
        self.assertIn("sheaf cokernel", quotient["scope"])
        ext = self.library["entries"]["COL-0392"]
        self.assertIn("cohomology", ext["scope"])
        incidence = self.library["entries"]["COL-0387"]
        self.assertIn(r"\operatorname{im}(s_T)\subseteq", incidence["statement"])
        self.assertIn("Tor", incidence["scope"])

    def test_motivic_chapter_keeps_actual_complex_and_evaluation_maps(self):
        chapters = {chapter["id"]: chapter for chapter in self.library["chapters"]}
        chapter = chapters["motivic-cohomology"]
        self.assertEqual(chapter["title"], "Motivic Cohomology")
        self.assertGreater(chapter["order"], chapters["cycles"]["order"])
        expected = {
            "reduced-transfer-tori": ["COL-0384", "COL-0385"],
            "canonical-motivic-complexes": ["COL-0398", "COL-1031", "COL-1037"],
            "motivic-hypercohomology": ["COL-0399", "COL-0400", "COL-1033"],
            "weight-one-norm": ["COL-0401"],
            "weight-one-comparison": [
                "COL-0402", "COL-0403", "COL-0404", "COL-1008", "COL-1007"
            ],
            "milnor-motivic-comparison": ["COL-1023"],
            "diagonal-motivic-comparison": ["COL-1025", "COL-1026"],
        }
        self.assertEqual(chapter["sections"], list(expected))
        for section_id, identifiers in expected.items():
            section = self.library["sections"][section_id]
            self.assertEqual(section["chapter"], "motivic-cohomology")
            self.assertEqual(section["entries"], identifiers)
            self.assertEqual(set(section["transitions"]), set(identifiers))
            for identifier in identifiers:
                self.assertEqual(self.library["entries"][identifier]["path"],
                                 f"docs/library/entries/motivic-cohomology/{identifier}.toml")
        for identifier, section_id in {
            "COL-0342": "derived-hom-comparisons",
            "COL-0394": "derived-hom-comparisons",
            "COL-0343": "nisnevich-sites",
            "COL-0395": "algebraic-simplices",
        }.items():
            self.assertEqual(self.library["entries"][identifier]["section"], section_id)
        complex_item = self.library["entries"]["COL-0398"]
        self.assertIn(r"(-1)^{qr}", complex_item["statement"])
        self.assertIn(r"(-1)^q", complex_item["statement"])
        self.assertIn("weight-one quasi-isomorphism", complex_item["scope"])
        hyper = self.library["entries"]["COL-0399"]
        self.assertIn(r"f^*(x)=x\circ(F_f[0])", hyper["statement"])
        base = self.library["entries"]["COL-0400"]
        self.assertIn(r"E_{p,q}^{-1}(z)=c\circ q_{K_q[p]}", base["statement"])
        self.assertIn("different universes", base["scope"])
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        output = self.render_site_fixture(built)
        self.assertTrue((output / "chapters/motivic-cohomology/index.html").is_file())
        for section_id, identifiers in expected.items():
            self.assertTrue((output / f"sections/{section_id}/index.html").is_file())
            for identifier in identifiers:
                page = (output / f"tag/{identifier}/index.html").read_text()
                self.assertIn('href="../../chapters/motivic-cohomology/">Motivic Cohomology</a>',
                              page)
                self.assertIn('class="scope-details"', page)
                declaration = built["declarations"][self.library["entries"][identifier]["primary"]]
                module, name = declaration["module"], declaration["name"]
                self.assertIn(f'href="../../modules/{module}/#{name}"', page)
                self.assertTrue((output / f"modules/{module}/index.html").is_file())
        records = json.loads((output / "search.json").read_text())
        for identifier in [identifier for ids in expected.values() for identifier in ids]:
            matches = [row for row in records if row.get("id") == identifier]
            self.assertEqual(len(matches), 1)
            self.assertEqual(matches[0]["path"], f"tag/{identifier}/")

    def test_weight_one_normalization_registration_and_binding_sources(self):
        # These are metadata fixtures, not evidence of native Lean elaboration.
        expected = {
            "COL-1008": (
                "Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.IntegralEquivalence",
                "AlgebraicGeometry.MotivicCohomology.WeightOne",
                "weightOneEquiv", "comparison", 40,
                ["motivicNorm", "weightOneEquiv", "motivicNorm_integralCycleClass",
                 "motivicNorm_integralGraphUnitClass", "weightOneEquiv_symm_apply",
                 "motivicNorm_eq_derivedWeightOneComparison"],
            ),
            "COL-1007": (
                "Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOne",
                "AlgebraicGeometry.MotivicCohomology.WeightOneFiniteCoefficients",
                "weightOneFiniteEquiv", "theorem", 50,
                ["weightOneFiniteEquiv", "weightOneFiniteEquiv_integralReduction",
                 "weightOneFiniteEquiv_symm_graph", "weightOneFiniteEquiv_symm_graphUnitClass",
                 "weightOneFiniteEquiv_graphUnitClass", "weightOneFiniteEquiv_cycleClass",
                 "finiteGraphUnitClass_eq_zero_iff_power"],
            ),
        }
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier, (module, namespace, primary, kind, order, names) in expected.items():
            item = self.library["entries"][identifier]
            self.assertEqual(item["section"], "weight-one-comparison")
            self.assertEqual(item["path"],
                             f"docs/library/entries/motivic-cohomology/{identifier}.toml")
            self.assertEqual((item["kind"], item["order"]), (kind, order))
            self.assertEqual(item["primary"], f"{namespace}.{primary}")
            self.assertEqual(built["declarations"][item["primary"]]["module"], module)
            source = (catalog.ROOT / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f"namespace {namespace}", source)
            if identifier == "COL-1008":
                bindings = re.findall(
                    r'@\[[^\]]*colib_tag "COL-1008"[^\]]*\]\s*(?:def|theorem)\s+(\w+)',
                    source,
                )
            else:
                groups = re.findall(
                    r'attribute \[colib_tag "COL-1007",[^\]]*\]\n((?:  \w+\n)+)',
                    source,
                )
                bindings = [name for group in groups for name in group.split()]
            self.assertEqual(bindings, names)
            for name in names:
                self.assertRegex(source, rf"\b(?:def|theorem)\s+{name}\b")
        transitions = self.library["sections"]["weight-one-comparison"]["transitions"]
        self.assertIn("COL-0403", transitions["COL-1008"])
        self.assertIn("COL-1008", transitions["COL-1007"])

    def test_weight_one_normalization_imports_and_consumers_are_discovered(self):
        modules = [
            "Colib.Algebra.Homology.Embedding.SingleComponent",
            "Colib.AlgebraicGeometry.Sites.Smooth.Units.UnitNormalization",
            "Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOne",
        ] + [
            f"Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.{leaf}"
            for leaf in ("ChainNormalization", "FieldComponent", "FieldEquivalence",
                         "IntegralEquivalence", "NormCoordinates", "PointNormalization",
                         "TargetNormalization")
        ]
        imports = (catalog.ROOT / "Colib.lean").read_text().splitlines()
        for module in modules:
            self.assertTrue((catalog.ROOT / (module.replace(".", "/") + ".lean")).is_file())
            self.assertEqual(imports.count(f"public import {module}"), 1)
        for leaf in ("ActualUnitNormalization", "ActualWeightOneNormCoordinates",
                     "WeightOneRecoveredComponents", "WeightOneRecoveredFieldNormalization",
                     "WeightOneRecoveredIntegralNormalization", "WeightOneRecoveredFiniteNormalization"):
            for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
                self.assert_test_in_checks(f"ColibTest.{leaf}", path)
        source = (catalog.ROOT / "ColibTest/WeightOneRecoveredFiniteNormalization.lean").read_text()
        self.assertEqual(len(re.findall(r"^example\b", source, re.M)), 11)
        for formula in ("weightOneFiniteEquiv k 0", "finiteGraphUnitClass k 0",
                        "subsingleton_level_one k", "weightOneFiniteEquiv k 6",
                        "[CharP k p]", "weightOneFiniteEquiv_cycleClass k n z"):
            self.assertIn(formula, source)

    def test_native_exterior_graph_identity_scope_and_outline(self):
        item = self.library["entries"]["COL-0388"]
        self.assertEqual(item["primary"], "Stacks.Chow.nativeExterior_graphFunctor")
        self.assertEqual(item["kind"], "theorem")
        self.assertEqual(item["proof_kind"], "outline")
        self.assertIn(r"E_T(\Gamma(\varphi))=\Gamma(\varphi\times\mathrm{id}_T)",
                      item["statement"])
        self.assertIn(r"E_T(1_X)=1_{X\times_kT}", item["statement"])
        self.assertIn("geometrically integral", item["statement"])
        self.assertIn("disconnected and empty", item["statement"])
        self.assertIn("coefficient one", item["statement"])
        self.assertIn("arbitrary correspondence composition", item["scope"])
        self.assertIn("matched-component Tor multiplicity", item["scope"])
        self.assertIn("parameter-product functor", item["scope"])
        self.assertIn("Graph.lean:176-222", item["scope"])
        self.assertIn("Unit.lean:151-193", item["scope"])
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        output = self.render_site_fixture(built)
        page = (output / "tag/COL-0388/index.html").read_text()
        self.assertIn("Colib.AlgebraicGeometry.Correspondences.Exterior.Graph", page)
        self.assertIn('<details class="proof"><summary>Proof outline</summary>', page)
        self.assertNotIn('<section class="proof"><h3>Proof</h3>', page)
        self.assertIn("Graph.lean#L176-L222", page)
        self.assertIn("Unit.lean#L151-L193", page)

    def test_cor_transfer_section_renders_maps_and_scope(self):
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        output = self.render_site_fixture(built)
        cor = (output / "sections/finite-correspondences/index.html").read_text()
        transfers = (output / "sections/transfers-nisnevich/index.html").read_text()
        self.assertIn('id="cycles-and-composition"', cor)
        self.assertIn('id="category-and-graphs"', cor)
        self.assertIn('id="sheafification-and-comparison"', transfers)
        self.assertIn('id="sheafification-and-affine-line"', transfers)
        self.assertIn("Stacks.Chow.incidenceTorPairing_assoc", cor)
        self.assertIn("AlgebraicGeometry.PresheafWithTransfers.nisnevichSheafificationUnderlyingIso",
                      transfers)
        self.assertIn(r"\Gamma(p_1)\circ\beta-\Gamma(p_2)\circ\beta", transfers)
        self.assertIn(r"c_P\circ\eta_{RP}=R(\eta_P)", transfers)
        self.assertIn("one neighborhood at each specified source point", transfers)
        self.assertIn('<details class="scope-details"><summary>Scope and conventions</summary>',
                      transfers)
        self.assertEqual(cor.count('class="section-transition"'), 6)
        self.assertEqual(transfers.count('class="section-transition"'), 7)
        coefficients = (output / "sections/finite-algebra-coefficients/index.html").read_text()
        self.assertIn('href="../../chapters/cycles/">Cycles and Correspondences</a>', cor)
        self.assertIn('href="../../chapters/transfers/">Presheaves and Sheaves with Transfers</a>',
                      transfers)
        self.assertIn('href="../../chapters/commutative-algebra/">Commutative Algebra</a>',
                      coefficients)
        self.assertIn('href="../../tag/COL-0340/">COL-0340</a>', cor)
        self.assertIn('href="../../tag/COL-0340/">COL-0340</a>', transfers)
        self.assertIn('href="../../tag/COL-0374/">COL-0374</a>', coefficients)
        records = json.loads((output / "search.json").read_text())
        for section_id in ("finite-correspondences", "transfers-nisnevich",
                           "finite-algebra-coefficients"):
            for identifier in self.library["sections"][section_id]["entries"]:
                self.assertTrue((output / f"tag/{identifier}/index.html").is_file())
                matches = [row for row in records if row.get("id") == identifier]
                self.assertEqual(len(matches), 1)
                self.assertEqual(matches[0]["path"], f"tag/{identifier}/")

    def test_perfect_waldhausen_chain_keeps_owners(self):
        self.assertEqual(self.library["entries"]["COL-0177"]["section"], "waldhausen-categories")
        self.assertEqual(self.library["entries"]["COL-0178"]["section"], "perfect-complexes")
        self.assertIn("every relevant pushout apex", self.library["entries"]["COL-0178"]["statement"])
        self.assertIn("No archived perfectness model", self.library["entries"]["COL-0178"]["scope"])
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in ("COL-0177", "COL-0178"):
            self.assertTrue(result["entries"][identifier]["references"])

    def test_perfect_local_comparison_is_retired(self):
        self.assertNotIn("COL-0176", self.library["entries"])
        self.assertEqual(self.library["retired"]["COL-0176"]["status"], "retired")
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        self.assertNotIn("COL-0176", result["entries"])
        self.assertIn("COL-0176", result["retired"])
        self.assertEqual(result["sections"]["perfect-complexes"]["modules"],
                         ["Colib.AlgebraicGeometry.Modules.PerfectWaldhausen"])

    def test_retired_id_cannot_be_reused(self):
        path = self.root / "docs/library/entries/algebraic-geometry/COL-0178.toml"
        path.write_text(path.read_text().replace('id = "COL-0178"', 'id = "COL-0176"'))
        with self.assertRaisesRegex(ValueError, "reused retired Library ID"):
            catalog.load_library(self.root)

    def test_retired_id_rejects_compiled_binding(self):
        native = self.native_fixture()
        native["bindings"].append({"id": "COL-0176", "name": native["declarations"][0]["name"]})
        with self.assertRaisesRegex(ValueError, "Unknown compiled Library binding"):
            catalog.compile_library(self.library, native, {}, "main")

    def test_retired_record_requires_safe_history(self):
        path = self.root / "docs/library/retired/COL-0176.toml"
        path.write_text(path.read_text().replace(
            'previous_path = "docs/library/entries/algebraic-geometry/COL-0176.toml"',
            'previous_path = "../../escape.toml"'))
        with self.assertRaisesRegex(ValueError, "previous Library path"):
            catalog.load_library(self.root)

    def render_site_fixture(self, built):
        spec = importlib.util.spec_from_file_location("colib_site", catalog.ROOT / "scripts/site.py")
        site = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(site)
        built["source_hashes"] = catalog.source_hashes()
        library_path = self.root / "library.json"
        library_path.write_text(json.dumps(built))
        output = self.root / "site"
        site.build(library_path, output)
        return output

    def test_retired_item_keeps_page_and_search_record(self):
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        output = self.render_site_fixture(built)
        page = (output / "tag/COL-0176/index.html").read_text()
        self.assertIn("Retired Library item", page)
        self.assertIn("5c0a7ab9c060b7482a3c49056bb9b3284fc47829", page)
        self.assertIn("COL-0178", page)
        records = json.loads((output / "search.json").read_text())
        retired = next(row for row in records if row.get("id") == "COL-0176")
        self.assertEqual(retired["kind"], "retired")
        self.assertEqual(retired["path"], "tag/COL-0176/")

    def test_site_preserves_navigation_rows_and_tex_source(self):
        native = self.native_fixture()
        name = next(b["name"] for b in native["bindings"] if b["id"] == "COL-0004")
        declaration = next(d for d in native["declarations"] if d["name"] == name)
        module = declaration["module"]
        source = catalog.ROOT / (module.replace(".", "/") + ".lean")
        line, code = next(
            (i, line) for i, line in enumerate(source.read_text().splitlines(), 1)
            if line.startswith("def fgModuleRankEquiv ")
        )
        declaration["source_range"] = [line, 0, line, len(code)]
        citation = next(ref for ref in native["citations"] if ref["name"] == name)
        citation["locator"] = "Tag 02MU"
        built = catalog.compile_library(self.library, native, {}, "main")
        item = built["entries"]["COL-0004"]
        item["statement"] = (
            r"Inline \(x < y\) and display \[\text{{revision}}\]. "
            "See [@stacks, Tag 02MU] and COL-0001. The code is `f <x>`."
            "\n\nA separate mathematical paragraph."
        )
        item["proof"] = "First proof paragraph.\n\nSecond proof paragraph."
        item["proof_kind"] = "proof"
        item["used_by"] = ["COL-0001"]
        item["formal_dependencies"] = ["COL-0001"]
        item["source_checked_on"] = "2026-11-05"
        section = built["sections"][item["section"]]
        section["transitions"] = {"COL-0004": r"Consider the case \(x < y\). See COL-0001."}
        output = self.render_site_fixture(built)
        page = (output / "tag/COL-0004/index.html").read_text()
        self.assertIn('href="../../chapters/k-theory-rings/">Algebraic K-Theory of Rings</a>', page)
        self.assertIn(
            f'href="../../sections/{section["id"]}/" aria-current="location">'
            '<span class="nav-section-title">',
            page,
        )
        self.assertIn('aria-label="Chapter contents"', page)
        self.assertIn('data-tex="x &lt; y"', page)
        self.assertIn(r'data-tex="\text{{revision}}"', page)
        self.assertIn('href="https://stacks.math.columbia.edu/tag/02MU">Tag 02MU</a>', page)
        self.assertIn('href="../../tag/COL-0001/">COL-0001</a>', page)
        self.assertIn("<code>f &lt;x&gt;</code>", page)
        self.assertIn("<p>A separate mathematical paragraph.</p>", page)
        self.assertIn(
            '<section class="proof"><h3>Proof</h3><p>First proof paragraph.</p>'
            "<p>Second proof paragraph.</p></section>",
            page,
        )
        correspondence = '<div class="item-details-body detail-stack">'
        self.assertEqual(page.count(correspondence), 1)
        identity = '<dl class="declaration-identity">'
        details = '<details class="item-details"><summary>Lean details</summary>'
        scope = '<details class="scope-details"><summary>Scope and conventions</summary>'
        order = [
            '<div class="item-statement"><header class="item-heading">',
            '<div class="statement">',
            '<section class="proof">',
            identity,
            '<p class="source-links">',
            scope,
            details,
            correspondence,
            '<footer class="item-references"><details><summary>References</summary>',
        ]
        positions = [page.index(element) for element in order]
        self.assertEqual(positions, sorted(positions))
        self.assertIn("</div></details>" + details, page)
        references = page.split('<footer class="item-references">', 1)[1].split("</footer>", 1)[0]
        self.assertIn('href="https://stacks.math.columbia.edu/tag/02MU">Tag 02MU</a>', references)
        self.assertIn('Metadata-validation fixture', references)
        self.assertEqual(references.count("<details"), 1)
        self.assertIn(f'data-copy="import {module}"', page)
        self.assertIn('<details class="source-code"><summary>Lean source</summary>', page)
        self.assertIn('<details class="relations"><summary>Referenced by</summary><p>', page)
        self.assertIn('<details class="relations"><summary>Direct Lean references</summary><p>', page)
        self.assertIn(f'Field.lean#L{line}"', page)
        self.assertIn(f'href="../../modules/{module}/#{name}"', page)
        self.assertIn('<code><span class="lean-keyword">def</span> fgModuleRankEquiv ', page)
        self.assertIn("Source correspondence · author-checked · 2026-11-05", page)
        section_page = (output / "sections" / section["id"] / "index.html").read_text()
        self.assertIn(f'href="../../sections/{section["id"]}/" aria-current="page"', section_page)
        transition = '<div class="section-transition"><p>Consider the case'
        self.assertLess(section_page.index(transition), section_page.index('<article class="item" id="COL-0004">'))
        self.assertNotIn(transition, page)
        chapter_page = (output / "chapters/category-theory/index.html").read_text()
        self.assertIn('<nav class="chapter-contents"', chapter_page)
        self.assertNotIn('tag/COL-0015/', chapter_page)
        exact = (output / "sections/exact-categories/index.html").read_text()
        self.assertIn('<section class="topic" id="conflations-and-base-change">', exact)
        self.assertIn('id="quillen-q-category"', exact)
        self.assertLess(exact.index('id="COL-0234"'), exact.index('id="COL-0038"'))
        self.assertRegex(
            exact,
            r'(?s)</article><div class="section-transition">.*?</div><article class="item" id="COL-0073">',
        )
        self.assertIn(details, exact)
        self.assertIn(scope, exact)
        records = json.loads((output / "search.json").read_text())
        result = next(row for row in records if row.get("id") == item["id"])
        self.assertEqual(result["statement"], item["statement"])
        self.assertIn('href="../tag/COL-0001/"', result["statement_html"])

    def test_lean_highlighting_preserves_source_text(self):
        source = '/- outer /- inner -/ end -/\n  def A.foo := "<x> -- /-"\n'
        rendered = lean_code.highlight(source)
        self.assertIn('<span class="lean-comment">/- outer /- inner -/ end -/</span>', rendered)
        self.assertIn('<span class="lean-keyword">def</span>', rendered)
        self.assertIn('<span class="lean-string">&quot;&lt;x&gt; -- /-&quot;</span>', rendered)
        self.assertEqual(unescape(re.sub(r"</?span\b[^>]*>", "", rendered)), source)

    def test_modules_tree_lists_colib_and_preserves_upstream_item_links(self):
        native = self.native_fixture()
        upstream = {
            "COL-0010": "Mathlib.RingTheory.LocalRing.Length",
            "COL-0001": "StacksCore.CategoryTheory.GrothendieckGroup.Basic",
            "COL-0005": "StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKTheory",
        }
        names = {binding["id"]: binding["name"] for binding in native["bindings"]}
        declarations = {row["name"]: row for row in native["declarations"]}
        for identifier, module in upstream.items():
            declarations[names[identifier]]["module"] = module
            native["modules"].append({"name": module, "imports": []})
        manifest = json.loads((catalog.ROOT / "lake-manifest.json").read_text())
        pins = {package["name"]: package for package in manifest["packages"]}
        built = catalog.compile_library(self.library, native, pins, "main")
        output = self.render_site_fixture(built)
        index = (output / "modules/index.html").read_text()
        self.assertIn('href="Colib.CategoryTheory.ExactCategory.Basic/"', index)
        for identifier, module in upstream.items():
            self.assertNotIn(f'href="{module}/"', index)
            page = (output / "tag" / identifier / "index.html").read_text()
            self.assertIn(f'href="../../modules/{module}/#{names[identifier]}"', page)
            detail = (output / "modules" / module / "index.html").read_text()
            self.assertIn(f'id="{names[identifier]}"', detail)

    def test_transition_requires_an_item_of_its_section(self):
        chapter = self.root / "docs/library/chapters/category-theory.toml"
        chapter.write_text(chapter.read_text() + '\nCOL-0015 = "A misplaced transition."\n')
        with self.assertRaisesRegex(ValueError, "must precede an item of the same section"):
            catalog.load_library(self.root)

    def test_prose_rejects_unresolved_links_and_unpaired_math(self):
        for text, message in (
            ("See [@Unknown].", "Unknown bibliography key"),
            ("See COL-9999.", "Unknown Library item"),
            ("See [@stacks, 02MU].", "Use Tag XXXX"),
            (r"Unclosed \(x", "closing delimiter"),
        ):
            with self.subTest(text=text):
                with self.assertRaisesRegex(ValueError, message):
                    catalog.check_prose(text, self.library, "fixture")
        catalog.check_prose(r"`[@Unknown]` and \(\text{COL-9999}\)", self.library, "fixture")

    def test_quillen_locators_preserve_repository_roots(self):
        source = self.library["sources"]["quillen"]
        base = source["url"].replace("/tree/", "/blob/")
        cases = (
            ("KTheory/Plus/StableGeneralLinearPlus.lean:31-57", "/Quillen/KTheory/Plus/StableGeneralLinearPlus.lean#L31-L57"),
            ("Quillen/KTheory/Plus/StableGeneralLinearPlus.lean:31-57", "/Quillen/KTheory/Plus/StableGeneralLinearPlus.lean#L31-L57"),
            ("examples/downstream/StableGeneralLinearPlus.lean", "/examples/downstream/StableGeneralLinearPlus.lean"),
        )
        for locator, expected in cases:
            with self.subTest(locator=locator):
                result = catalog.reference_locations("quillen", source, locator)
                self.assertEqual(result[0]["url"], base + expected)
        self.assertEqual(catalog.reference_locations("quillen", source, "Section 7")[0]["url"], source["url"])
        for locator in ("Quillen//Test.lean:1", "Quillen/../Test.lean:1", "KTheory/Test.lean:9-7", "examples/Test.lean:0"):
            with self.subTest(locator=locator), self.assertRaises(ValueError):
                catalog.reference_locations("quillen", source, locator)

    def test_software_locators_link_each_span_at_the_recorded_commit(self):
        source = self.library["sources"]["aglib_principal_euler_pin"]
        locator = "Algebra/Homology/DerivedCategory/ExtRightDerived.lean:220-258,336-433"
        locations = catalog.reference_locations("aglib_principal_euler_pin", source, locator)
        base = source["url"].replace("/tree/", "/blob/") + "/Aglib/" + locator.split(":")[0]
        self.assertEqual([item["url"] for item in locations], [
            base + "#L220-L258",
            base + "#L336-L433",
        ])
        with self.assertRaisesRegex(ValueError, "Invalid line range"):
            catalog.reference_locations("aglib_principal_euler_pin", source, "Aglib/Test.lean:9-7")
        with self.assertRaisesRegex(ValueError, "Invalid line range"):
            catalog.reference_locations("aglib_principal_euler_pin", source, "Aglib/Test.lean:12-")

    def test_perfect_regressions_use_only_native_objects(self):
        root = catalog.ROOT
        for stem in ("LocalRepresentativeComparison", "LocalRepresentativeEquivalence"):
            self.assertFalse((root / "Colib/AlgebraicGeometry/Modules" / (stem + ".lean")).exists())
            self.assertNotIn(stem, (root / "Colib.lean").read_text())
        for stem in ("PerfectLocalComparison", "PerfectLocalEquivalence", "PerfectKEquivalence"):
            self.assertFalse((root / "ColibTest" / (stem + ".lean")).exists())
            self.assertNotIn("ColibTest." + stem, lint_style.source_modules(root, "ColibTest"))
        for stem in ("PerfectWaldhausen", "PerfectKTheory"):
            source = (root / "ColibTest" / (stem + ".lean")).read_text()
            self.assertIn("RingedSpace.perfectComplexesWaldhausen", source)
            self.assertNotIn("import all", source)
            self.assertNotIn("private def source", source)
            self.assert_test_in_checks("ColibTest." + stem, "scripts/check.sh")

    def test_waldhausen_homotopy_chain_keeps_model_and_owners(self):
        self.assertEqual(self.library["entries"]["COL-0154"]["section"], "waldhausen-categories")
        for number in range(155, 159):
            self.assertEqual(
                self.library["entries"][f"COL-{number:04d}"]["section"], "waldhausen-k-theory"
            )
        self.assertIn("unnormalized", self.library["entries"]["COL-0146"]["scope"])
        self.assertIn("strict chosen-zero", self.library["entries"]["COL-0154"]["scope"])
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for number in range(154, 159):
            self.assertTrue(result["entries"][f"COL-{number:04d}"]["references"])

    def test_three_route_chains_keep_grouped_owners(self):
        for identifier, section in (
            ("COL-0144", "waldhausen-categories"),
            ("COL-0145", "waldhausen-categories"),
            ("COL-0146", "waldhausen-categories"),
            ("COL-0147", "homology-colimits"),
            ("COL-0148", "homology-colimits"),
            ("COL-0149", "affine-open-pairs"),
        ):
            self.assertEqual(self.library["entries"][identifier]["section"], section)
        catalog.compile_library(self.library, self.native_fixture(), {}, "main")

    def test_nerve_cylinder_and_native_simplex_owners_survive_adapter_retirement(self):
        owners = {
            "COL-0058": ("classifying-spaces", "Colib.Topology.ClassifyingSpace.NerveHomotopy"),
            "COL-0082": ("geometric-realization", "Colib.Analysis.Convex.StdSimplex.PathHomotopy"),
            "COL-0098": ("geometric-realization",
                         "Colib.Analysis.Convex.StdSimplex.BoundaryRetraction"),
        }
        root = catalog.ROOT
        root_imports = (root / "Colib.lean").read_text()
        for identifier, (section, module) in owners.items():
            self.assertEqual(self.library["entries"][identifier]["section"], section)
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn("public import " + module, root_imports)
            if identifier != "COL-0058":
                self.assertIn("namespace Convexity.StdSimplex", source)
                self.assertIn("StdSimplex ℝ", source)
                self.assertNotIn("_root_.stdSimplex", source)

        self.assertNotIn("COL-0059", self.library["entries"])
        retired = self.library["retired"]["COL-0059"]
        self.assertEqual(retired["status"], "retired")
        self.assertEqual(retired["previous_path"], "docs/library/entries/topology/COL-0059.toml")
        self.assertEqual(retired["related_items"], ["COL-0082", "COL-0098"])
        self.assertFalse((root / retired["previous_path"]).exists())
        obsolete_module = "Colib.Topology.Realization.FiniteSimplexAdapter"
        self.assertFalse((root / (obsolete_module.replace(".", "/") + ".lean")).exists())
        self.assertNotIn(obsolete_module, root_imports)
        for path in (root / "Colib").rglob("*.lean"):
            source = path.read_text()
            self.assertNotIn(obsolete_module, source, str(path))
            self.assertNotIn('colib_tag "COL-0059"', source, str(path))

        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        self.assertEqual(
            result["sections"]["geometric-realization"]["modules"],
            sorted(owners[identifier][1] for identifier in ("COL-0082", "COL-0098")),
        )
        for identifier, (_, module) in owners.items():
            self.assertTrue(result["entries"][identifier]["references"])
            declarations = result["entries"][identifier]["declarations"]
            self.assertTrue(declarations)
            self.assertEqual({result["declarations"][name]["module"] for name in declarations},
                             {module})
        self.assertNotIn("COL-0059", result["entries"])
        self.assertIn("COL-0059", result["retired"])
        self.assertNotIn(obsolete_module, result["modules"])

        native = self.native_fixture()
        native["bindings"].append({"id": "COL-0059", "name": native["declarations"][0]["name"]})
        with self.assertRaisesRegex(ValueError, "Unknown compiled Library binding"):
            catalog.compile_library(self.library, native, {}, "main")
        entry = self.root / "docs/library/entries/topology/COL-0082.toml"
        entry.write_text(entry.read_text().replace('id = "COL-0082"', 'id = "COL-0059"'))
        with self.assertRaisesRegex(ValueError, "reused retired Library ID"):
            catalog.load_library(self.root)

    def test_realization_prerequisite_ids_keep_their_owners(self):
        for index in range(60, 65):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(60, 65):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_finite_prism_id_keeps_its_owner(self):
        self.assertEqual(
            self.library["entries"]["COL-0065"]["section"], "geometric-realization"
        )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        self.assertTrue(result["entries"]["COL-0065"]["references"])

    def test_realized_standard_prism_ids_keep_their_owners(self):
        for identifier in ("COL-0066", "COL-0067"):
            self.assertEqual(
                self.library["entries"][identifier]["section"], "geometric-realization"
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in ("COL-0066", "COL-0067"):
            self.assertTrue(result["entries"][identifier]["references"])

    def test_realization_bridge_ids_keep_their_owners(self):
        for index in range(68, 71):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(68, 71):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_based_invariance_and_kmap_composition_ids_keep_their_owners(self):
        for identifier, section in (
            ("COL-0071", "homotopy-groups"),
            ("COL-0072", 'quillen-k-theory'),
        ):
            self.assertEqual(self.library["entries"][identifier]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in ("COL-0071", "COL-0072"):
            self.assertTrue(result["entries"][identifier]["references"])

    def test_split_kernel_and_q_object_class_ids_keep_their_owners(self):
        for index in range(73, 76):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"], "exact-categories"
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(73, 76):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_algebraic_q_groupoid_ids_keep_their_owners(self):
        for index in range(76, 81):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "exact-categories" if index < 78 else "grothendieck-groups" if index == 78 else "quillen-k-theory",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(76, 81):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_object_loop_bridge_ids_keep_their_owners(self):
        for index in range(81, 87):
            section = (
                "geometric-realization" if index < 84 else
                "classifying-spaces" if index < 86 else "quillen-k-theory"
            )
            self.assertEqual(self.library["entries"][f"COL-{index:04d}"]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(81, 87):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_open_cover_and_sequential_colimit_ids_keep_their_owners(self):
        for index in range(87, 90):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"], "homotopy-groups"
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(87, 90):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_constant_realization_and_completion_ids_keep_their_owners(self):
        for index in range(90, 94):
            section = "geometric-realization" if index < 92 else "classifying-spaces"
            self.assertEqual(self.library["entries"][f"COL-{index:04d}"]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(90, 94):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_pushout_and_open_cover_full_ids_keep_their_owners(self):
        for index in range(94, 98):
            section = "functor-constructions" if index == 96 else "homotopy-groups"
            self.assertEqual(self.library["entries"][f"COL-{index:04d}"]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(94, 98):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_simplex_boundary_and_collar_ids_keep_their_owners(self):
        for index in range(98, 100):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(98, 100):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_simplex_charts_and_annulus_ids_keep_their_owners(self):
        for index in range(100, 102):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(100, 102):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_simplex_attachment_collar_ids_keep_their_owners(self):
        for index in range(102, 104):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(102, 104):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_attachment_cover_generation_fullness_ids_keep_their_owners(self):
        for index in range(104, 107):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(104, 107):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_boundary_endpoints_and_graph_anchors_ids_keep_their_owners(self):
        for index in range(107, 109):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(107, 109):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_initial_ids_keep_their_owners(self):
        self.assertTrue(
            {f"COL-{index:04d}" for index in range(1, 13)}
            <= self.library["entries"].keys()
        )
        self.assertEqual(
            self.library["entries"]["COL-0004"]["section"], "k-zero-of-fields"
        )

    def test_exact_foundations_and_k0_ids_keep_their_owners(self):
        for index in range(15, 18):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "exact-categories",
            )
        for index in range(18, 20):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "grothendieck-groups",
            )
        self.assertEqual(self.library["entries"]["COL-0020"]["section"], "k-zero-of-fields")
        native = self.native_fixture()
        result = catalog.compile_library(self.library, native, {}, "main")
        self.assertEqual(
            result["sections"]["exact-categories"]["modules"],
            ["Colib.CategoryTheory.ExactCategory.Basic"],
        )

    def test_exact_functor_and_subgroup_ids_keep_their_owners(self):
        self.assertEqual(
            self.library["entries"]["COL-0023"]["section"], "exact-categories"
        )
        for index in range(24, 27):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "grothendieck-groups",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(23, 27):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_serre_localization_ids_keep_their_owners(self):
        self.assertEqual(
            self.library["entries"]["COL-0027"]["section"], "exact-categories"
        )
        for index in (28, 29):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "resolution-devissage-and-serre-localization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(27, 30):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_admissible_pullback_ids_keep_their_owners(self):
        for index in (32, 33):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "exact-categories",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in (32, 33):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_quotient_and_restricted_span_ids_keep_their_owners(self):
        self.assertEqual(self.library["entries"]["COL-0034"]["section"], "bicategories")
        self.assertEqual(self.library["entries"]["COL-0035"]["section"], "restricted-spans")
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in ("COL-0034", "COL-0035"):
            self.assertTrue(result["entries"][identifier]["references"])

    def test_q_functoriality_ids_keep_their_owners(self):
        self.assertEqual(self.library["entries"]["COL-0036"]["section"], "restricted-spans")
        self.assertEqual(self.library["entries"]["COL-0037"]["section"], "exact-categories")
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in ("COL-0036", "COL-0037"):
            self.assertTrue(result["entries"][identifier]["references"])

    def test_q_connectedness_ids_keep_their_owners(self):
        for index in (38, 39, 40):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "exact-categories",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in (38, 39, 40):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_quillen_homotopy_ids_keep_their_owners(self):
        owners = {43: "classifying-spaces", 44: "restricted-spans", 45: "quillen-k-theory"}
        for index, section in owners.items():
            self.assertEqual(self.library["entries"][f"COL-{index:04d}"]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in owners:
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_q_core_ids_keep_their_owners(self):
        self.assertEqual(self.library["entries"]["COL-0046"]["section"], "restricted-spans")
        for index in range(47, 51):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"], "exact-categories"
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(46, 51):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_quillen_map_ids_keep_their_owners(self):
        owners = {
            51: "functor-constructions", 52: "homotopy-groups",
            53: "classifying-spaces", 54: "classifying-spaces", 55: "quillen-k-theory",
        }
        for index, section in owners.items():
            self.assertEqual(self.library["entries"][f"COL-{index:04d}"]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in owners:
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_normalized_q_ids_keep_their_owners(self):
        self.assertEqual(self.library["entries"]["COL-0056"]["section"], "functor-constructions")
        self.assertEqual(self.library["entries"]["COL-0057"]["section"], "exact-categories")
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in ("COL-0056", "COL-0057"):
            self.assertTrue(result["entries"][identifier]["references"])

    def test_unknown_reference_is_rejected(self):
        native = self.native_fixture()
        native["citations"][0]["source"] = "missing"
        with self.assertRaisesRegex(ValueError, "Unknown bibliographic key"):
            catalog.compile_library(self.library, native, {}, "main")

    def test_item_requires_a_compiled_binding(self):
        native = self.native_fixture()
        native["bindings"].pop()
        with self.assertRaisesRegex(ValueError, "needs a compiled"):
            catalog.compile_library(self.library, native, {}, "main")

    def test_multiple_literature_references_are_retained(self):
        native = self.native_fixture()
        extra = dict(
            native["citations"][0], source="WeibelKBook", locator="II, Definition 6.1.1"
        )
        native["citations"].append(extra)
        result = catalog.compile_library(self.library, native, {}, "main")
        identifier = native["bindings"][0]["id"]
        self.assertEqual(
            {ref["source"] for ref in result["entries"][identifier]["references"]},
            {"stacks", "WeibelKBook"},
        )

    def test_citation_does_not_require_a_permanent_item_tag(self):
        native = self.native_fixture()
        native["declarations"].append(
            {
                "name": "CategoryTheory.helper",
                "type": "Prop",
                "module": "Colib.RingTheory.KTheory.GrothendieckGroup.Field",
                "dependencies": [],
            }
        )
        native["citations"].append(
            {
                "name": "CategoryTheory.helper",
                "source": "WeibelKBook",
                "locator": "II, section 2",
                "relation": "ingredient",
                "scope": "Fixture",
            }
        )
        result = catalog.compile_library(self.library, native, {}, "main")
        self.assertTrue(
            any(ref["name"] == "CategoryTheory.helper" for ref in result["citations"])
        )
        self.assertFalse(
            any(
                "CategoryTheory.helper" in item["declarations"]
                for item in result["entries"].values()
            )
        )

    def test_duplicate_id_is_rejected(self):
        path = self.root / "docs/library/entries/k-theory/COL-0002.toml"
        path.write_text(path.read_text().replace('id = "COL-0002"', 'id = "COL-0001"'))
        with self.assertRaisesRegex(ValueError, "duplicate Library ID"):
            catalog.load_library(self.root)

    def test_hand_maintained_dependencies_are_rejected(self):
        path = self.root / "docs/library/entries/k-theory/COL-0001.toml"
        path.write_text(path.read_text() + 'requires = ["COL-0002"]\n')
        with self.assertRaisesRegex(ValueError, "dependencies come from Lean"):
            catalog.load_library(self.root)

    def test_hand_maintained_module_routes_are_rejected(self):
        path = self.root / "docs/library/chapters/k-theory.toml"
        path.write_text(path.read_text().replace(
            'id = "bass-delooping-diagrams-and-functoriality"\n',
            'id = "bass-delooping-diagrams-and-functoriality"\nmodules = ["Colib.KTheory"]\n',
            1,
        ))
        with self.assertRaisesRegex(ValueError, "Module ownership is exported"):
            catalog.load_library(self.root)

    def test_module_ownership_is_exported(self):
        native = self.native_fixture()
        result = catalog.compile_library(self.library, native, {}, "main")
        self.assertIn(
            "Colib.RingTheory.KTheory.GrothendieckGroup.Field",
            result["sections"]["k-zero-of-fields"]["modules"],
        )

    def test_declaration_lists_are_owned_by_lean(self):
        path = self.root / "docs/library/entries/k-theory/COL-0001.toml"
        path.write_text(
            path.read_text() + 'declarations = ["CategoryTheory.GrothendieckGroup"]\n'
        )
        with self.assertRaisesRegex(ValueError, "belong in Lean attributes"):
            catalog.load_library(self.root)

    def test_editorial_move_retains_the_lean_defining_module(self):
        shutil.copytree(catalog.ROOT / "Colib", self.root / "Colib")
        for name in (
            "Colib.lean",
            "lakefile.toml",
            "lake-manifest.json",
            "lean-toolchain",
        ):
            shutil.copyfile(catalog.ROOT / name, self.root / name)
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        built["source_hashes"] = catalog.source_hashes(self.root)
        directory = self.root / "build/library"
        directory.mkdir(parents=True)
        (directory / "library.json").write_text(json.dumps(built))
        entry = self.root / "docs/library/entries/k-theory-rings/COL-0004.toml"
        entry.write_text(
            entry.read_text().replace(
                'section = "k-zero-of-fields"', 'section = "milnor-symbols-field-change"'
            )
        )
        scripts = self.root / "scripts"
        scripts.mkdir()
        for name in ("catalog.py", "library_text.py"):
            shutil.copyfile(catalog.ROOT / "scripts" / name, scripts / name)
        result = subprocess.run(
            [sys.executable, str(scripts / "catalog.py"), "show", "COL-0004"],
            check=True,
            capture_output=True,
            text=True,
        )
        item = json.loads(result.stdout)
        self.assertEqual(item["chapter"], "milnor-k-theory")
        self.assertEqual(item["section"], "milnor-symbols-field-change")
        self.assertEqual(item["modules"], ["Colib.RingTheory.KTheory.GrothendieckGroup.Field"])

    def test_unsafe_bibliographic_path_is_rejected(self):
        path = self.root / "docs/references.toml"
        path.write_text(path.read_text() + '\n[sources."../../escape"]\n')
        with self.assertRaisesRegex(ValueError, "Unsafe bibliographic key"):
            catalog.load_library(self.root)

    def test_unknown_source_provider_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "Unsupported catalog source"):
            catalog.source_link("OtherLibrary.Result", {}, "main")


    def test_reconstructed_quillen_topics_keep_chapter_owners(self):
        expected = {'COL-0517': ['k-theory', 'bass-delooping-diagrams-and-functoriality'], 'COL-0513': ['k-theory-rings', 'quillen-k-theory-of-rings'], 'COL-0507': ['k-theory-schemes', 'support-and-connective-localization'], 'COL-0511': ['k-theory-schemes', 'affine-and-global-section-models'], 'COL-0510': ['k-theory-schemes', 'bass-k-theory-and-geometric-delooping'], 'COL-0518': ['topology', 'homotopy-groups']}
        for identifier, (chapter, section) in expected.items():
            item = self.library["entries"][identifier]
            self.assertEqual(item["section"], section)
            self.assertEqual(item["path"],
                             f"docs/library/entries/{chapter}/{identifier}.toml")


    def test_tt_successor_topics_keep_chapter_owners(self):
        expected = {'COL-0519': ('bass-delooping-diagrams-and-functoriality', 'docs/library/entries/k-theory/COL-0519.toml'), 'COL-0520': ('homotopy-groups', 'docs/library/entries/topology/COL-0520.toml'), 'COL-0521': ('bass-delooping-diagrams-and-functoriality', 'docs/library/entries/k-theory/COL-0521.toml'), 'COL-0522': ('homotopy-groups', 'docs/library/entries/topology/COL-0522.toml'), 'COL-0523': ('bass-delooping-diagrams-and-functoriality', 'docs/library/entries/k-theory/COL-0523.toml'), 'COL-0524': ('homotopy-groups', 'docs/library/entries/topology/COL-0524.toml'), 'COL-0525': ('bass-delooping-diagrams-and-functoriality', 'docs/library/entries/k-theory/COL-0525.toml'), 'COL-0526': ('homotopy-groups', 'docs/library/entries/topology/COL-0526.toml'), 'COL-0527': ('bass-delooping-diagrams-and-functoriality', 'docs/library/entries/k-theory/COL-0527.toml'), 'COL-0528': ('bass-delooping-diagrams-and-functoriality', 'docs/library/entries/k-theory/COL-0528.toml'), 'COL-0529': ('bass-delooping-diagrams-and-functoriality', 'docs/library/entries/k-theory/COL-0529.toml'), 'COL-0530': ('bass-delooping-diagrams-and-functoriality', 'docs/library/entries/k-theory/COL-0530.toml'), 'COL-0531': ('bass-delooping-diagrams-and-functoriality', 'docs/library/entries/k-theory/COL-0531.toml'), 'COL-0532': ('scheme-products-and-index-squares', 'docs/library/entries/algebraic-geometry/COL-0532.toml')}
        for identifier, (section, path) in expected.items():
            item = self.library["entries"][identifier]
            self.assertEqual(item["section"], section)
            self.assertEqual(item["path"], path)


    def test_global_scheme_geometry_items_keep_scope_and_owners(self):
        expected = {'COL-0533': ('k-theory-schemes', 'affine-and-global-section-models'), 'COL-0534': ('k-theory-schemes', 'affine-and-global-section-models'), 'COL-0535': ('k-theory-schemes', 'affine-and-global-section-models'), 'COL-0536': ('algebraic-geometry', 'scheme-products-and-index-squares'), 'COL-0537': ('k-theory-schemes', 'affine-and-global-section-models')}
        for identifier, (chapter, section) in expected.items():
            item = self.library["entries"][identifier]
            self.assertEqual(item["section"], section)
            self.assertEqual(item["path"], f"docs/library/entries/{chapter}/{identifier}.toml")
        self.assertIn("not a returned", self.library["entries"]["COL-0537"]["scope"])
        self.assertIn("does not yet bundle", self.library["entries"]["COL-0535"]["scope"])


    def test_joint_models_and_laurent_tracks_keep_scheme_owner(self):
        for identifier in ['COL-0538', 'COL-0539', 'COL-0540', 'COL-0541']:
            item = self.library["entries"][identifier]
            self.assertEqual(item["section"], "affine-and-global-section-models")
            self.assertEqual(item["path"], f"docs/library/entries/k-theory-schemes/{identifier}.toml")


    def test_tensor_unit_prisms_keep_scheme_owner(self):
        for identifier in ['COL-0542', 'COL-0543', 'COL-0544', 'COL-0545', 'COL-0546', 'COL-0547']:
            item = self.library["entries"][identifier]
            self.assertEqual(item["section"], "units-tensor-products-and-localization-boundaries")
            self.assertEqual(item["path"], f"docs/library/entries/k-theory-schemes/{identifier}.toml")



    def test_returned_geometric_items_keep_owners_and_primaries(self):
        expected = {'COL-0548': {'chapter': 'k-theory-schemes',
                      'section': 'affine-and-global-section-models',
                      'primary': 'AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.evaluationModel_isStableEquivalence',
                      'module': 'Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationEquivalence'},
         'COL-0549': {'chapter': 'k-theory',
                      'section': 'bass-delooping-normalization-and-telescopes',
                      'primary': 'Topology.LoopPrespectrum.RowRefinement.normalizedOperation',
                      'module': 'Colib.Topology.Prespectrum.RowNormalizedOperation'},
         'COL-0550': {'chapter': 'k-theory-schemes',
                      'section': 'bass-k-theory-and-geometric-delooping',
                      'primary': 'AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow.returnedPasting',
                      'module': 'Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorReturnedCell'},
         'COL-0551': {'chapter': 'k-theory-schemes',
                      'section': 'bass-k-theory-and-geometric-delooping',
                      'primary': 'AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow.strictifiedNormalizedForward_eq',
                      'module': 'Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorReturnedStrictification'}}
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier, want in expected.items():
            item = self.library["entries"][identifier]
            self.assertEqual(item["section"], want["section"])
            self.assertEqual(item["path"],
                             f"docs/library/entries/{want['chapter']}/{identifier}.toml")
            self.assertEqual(item["primary"], want["primary"])
            declaration = built["declarations"][want["primary"]]
            self.assertEqual(declaration["module"], want["module"])

    def test_current_boundary_items_keep_owners_and_primaries(self):
        expected = (
            (
                "COL-0552", "k-theory", 'bass-delooping-normalization-and-telescopes',
                "KTheory.Bass.DiagramRowSeed.normalizedBoundaryHomotopy",
                "Colib.KTheory.Bass.DiagramRowNormalizedBoundaryHomotopy",
                "Quillen/KTheory/Bass/DiagramRowNormalizedBoundary.lean:74",
            ),
            (
                "COL-0553", "k-theory", 'bass-delooping-normalization-and-telescopes',
                "KTheory.Bass.ModelRowZigzagSequentialization.backward_eq",
                "Colib.KTheory.Bass.ModelRowZigzagBackward",
                "Quillen/KTheory/Bass/ModelRowZigzagSequentialization.lean:45",
            ),
            (
                "COL-0554", "k-theory", 'bass-delooping-normalization-and-telescopes',
                "KTheory.Bass.WholeSeedCospan.seed",
                "Colib.KTheory.Bass.WholeSeedWord",
                "Quillen/KTheory/Bass/WholeSeedCospan.lean:76",
            ),
            (
                "COL-0555", "k-theory-schemes", 'bass-k-theory-and-geometric-delooping',
                "KTheory.Bass.SchemeModelRowSeed.normalizedBoundaryCurrentHomotopy",
                "Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowCurrentBoundary",
                "Quillen/KTheory/Bass/SchemeModelRowNormalizedBoundary.lean:57",
            ),
        )
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier, chapter, section, primary, module, locator in expected:
            with self.subTest(identifier=identifier):
                item = self.library["entries"][identifier]
                self.assertEqual(item["section"], section)
                self.assertEqual(item["path"],
                                 f"docs/library/entries/{chapter}/{identifier}.toml")
                self.assertEqual(item["primary"], primary)
                self.assertEqual(built["declarations"][primary]["module"], module)
                source = (catalog.ROOT / (module.replace(".", "/") + ".lean")).read_text()
                self.assertIn(f'attribute [colib_tag "{identifier}"]\n  {primary}', source)
                self.assertIn(f'"{locator}"', source)
                self.assertNotIn("Quillen c561118b:", source)


    def test_returned_recognition_items_keep_owners_and_primaries(self):
        expected = [('COL-0556', 'units-tensor-products-and-localization-boundaries', 'AlgebraicGeometry.Scheme.Modules.tensorUnitCoefficientKOneClass_inclusion', 'Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientKOne'), ('COL-0557', 'bass-k-theory-and-geometric-delooping', 'AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition.tensorSquare_unique', 'Colib.AlgebraicGeometry.KTheory.BoundedFlatReturnedTensorGenerators'), ('COL-0558', 'bass-k-theory-and-geometric-delooping', 'AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition.tensor_generated_trace', 'Colib.AlgebraicGeometry.KTheory.BoundedFlatReturnedTensorGeneratedTrace')]
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier, section, primary, module in expected:
            item = self.library["entries"][identifier]
            self.assertEqual(item["section"], section)
            self.assertEqual(item["path"], f"docs/library/entries/k-theory-schemes/{identifier}.toml")
            self.assertEqual(item["primary"], primary)
            self.assertEqual(built["declarations"][primary]["module"], module)


    def test_supported_forget_items_keep_native_owners(self):
        expected = [
            (
                'COL-0559',
                'functor-constructions',
                'CategoryTheory.Functor.isoSquareTargetNormalization_rectangle',
                'Colib.CategoryTheory.Functor.IsoRouteTargetNormalization',
                'category-theory',
            ),
            (
                'COL-0560',
                'units-tensor-products-and-localization-boundaries',
                'AlgebraicGeometry.Scheme.Modules.GlobalTensorNormalizedSupport.supportedUnit_naturality',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalTensorNormalizedSupport',
                'k-theory-schemes',
            ),
            (
                'COL-0561',
                'units-tensor-products-and-localization-boundaries',
                'AlgebraicGeometry.Scheme.Modules.boundedAboveFlatPerfectSupportedTensorUnitFirstRow_exact',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedCoefficientExact',
                'k-theory-schemes',
            ),
            (
                'COL-0562',
                'units-tensor-products-and-localization-boundaries',
                'AlgebraicGeometry.Scheme.Modules.tensorSupportedPairSmallCoefficientCylinder_eq',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedCoefficientSmallCylinder',
                'k-theory-schemes',
            ),
            (
                'COL-0563',
                'units-tensor-products-and-localization-boundaries',
                'AlgebraicGeometry.Scheme.Modules.ParameterTensorSupportedRow.modelEvaluationForgetRectangle',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorSupportedForgetRectangle',
                'k-theory-schemes',
            ),
        ]
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier, section, primary, module, folder in expected:
            item = self.library["entries"][identifier]
            self.assertEqual(item["section"], section)
            self.assertEqual(item["path"], f"docs/library/entries/{folder}/{identifier}.toml")
            self.assertEqual(item["primary"], primary)
            self.assertEqual(built["declarations"][primary]["module"], module)


    def test_current_normalized_fiber_items_keep_native_owners(self):
        expected = [
            (
                'COL-0564',
                'homotopy-colimits',
                'Topology.LoopPrespectrum.ZigzagSequentialization.telescopeToOrdinaryColimit_isStableEquivalence',
                'Colib.Topology.Prespectrum.ZigzagSequentializationColimit',
                'topology',
            ),
            (
                'COL-0565',
                'bass-delooping-normalization-and-telescopes',
                'KTheory.Bass.NormalizedStageMap.model_stageMap_stable',
                'Colib.KTheory.Bass.NormalizedStageMapStable',
                'k-theory',
            ),
            (
                'COL-0566',
                'thomason-trobaugh-localization',
                'KTheory.Bass.SchemeNaturalSeed.model_telescopeMap_stable',
                'Colib.AlgebraicGeometry.KTheory.Bass.SchemeCurrentStageTelescopeStable',
                'k-theory-schemes',
            ),
            (
                'COL-0567',
                'bass-delooping-normalization-and-telescopes',
                'KTheory.Bass.NormalizedStageMap.stageMap_null',
                'Colib.KTheory.Bass.NormalizedDiagramNull',
                'k-theory',
            ),
            (
                'COL-0568',
                'thomason-trobaugh-localization',
                'AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull.current_null_square',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullCurrentNull',
                'k-theory-schemes',
            ),
            (
                'COL-0569',
                'thomason-trobaugh-localization',
                'AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport.current_null_square',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryCurrentNull',
                'k-theory-schemes',
            ),
            (
                'COL-0570',
                'thomason-trobaugh-localization',
                'AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull.current_normalized_lift_stable_iff',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullCurrentFiberComparison',
                'k-theory-schemes',
            ),
        ]
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier, section, primary, module, folder in expected:
            item = self.library["entries"][identifier]
            self.assertEqual(item["section"], section)
            self.assertEqual(item["path"], f"docs/library/entries/{folder}/{identifier}.toml")
            self.assertEqual(item["primary"], primary)
            self.assertEqual(built["declarations"][primary]["module"], module)


    def test_normalized_twisted_fiber_items_keep_native_owners(self):
        expected = [
            (
                'COL-0571',
                'homotopy-colimits',
                'Topology.LoopPrespectrum.StrictSquare.coneInterchangeIso',
                'Colib.Topology.Prespectrum.StrictSquareConeInterchange',
                'topology',
            ),
            (
                'COL-0572',
                'thomason-trobaugh-localization',
                'KTheory.Bass.GeometricConeInterchange.permutationFunctorIso',
                'Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeSchemeNaturality',
                'k-theory-schemes',
            ),
            (
                'COL-0573',
                'thomason-trobaugh-localization',
                'KTheory.Bass.SchemeNaturalSeed.model_conjugacyTelescopeMap_stable',
                'Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedTelescope',
                'k-theory-schemes',
            ),
            (
                'COL-0574',
                'thomason-trobaugh-localization',
                'KTheory.Bass.SchemeNaturalSeed.conjugacyTelescopeMap_null',
                'Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedNull',
                'k-theory-schemes',
            ),
            (
                'COL-0575',
                'thomason-trobaugh-localization',
                'AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull.normalized_twisted_lift_stable_iff',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullTwistedFiberComparison',
                'k-theory-schemes',
            ),
        ]
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier, section, primary, module, folder in expected:
            item = self.library["entries"][identifier]
            self.assertEqual(item["section"], section)
            self.assertEqual(item["path"], f"docs/library/entries/{folder}/{identifier}.toml")
            self.assertEqual(item["primary"], primary)
            self.assertEqual(built["declarations"][primary]["module"], module)


    def test_integral_spec_fine_items_keep_native_owners(self):
        expected = [
            (
                'COL-0576',
                'bass-delooping-normalization-and-telescopes',
                'KTheory.Bass.StrictDiagramIndexRow.telescopeIso',
                'Colib.KTheory.Bass.StrictDiagramIndexRowTelescope',
                'k-theory',
            ),
            (
                'COL-0577',
                'bass-delooping-diagrams-and-functoriality',
                'KTheory.Bass.modelDiagramIterate_map_isStableEquivalence_of_exactEquivalence',
                'Colib.KTheory.Bass.ModelDiagramStableEquivalence',
                'k-theory',
            ),
            (
                'COL-0578',
                'scheme-products-and-index-squares',
                'AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec.specSquare',
                'Colib.AlgebraicGeometry.Scheme.IntegerBaseSpecSquare',
                'algebraic-geometry',
            ),
            (
                'COL-0579',
                'thomason-trobaugh-localization',
                'AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.telescopeRestriction_isStableEquivalence',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionTelescope',
                'k-theory-schemes',
            ),
            (
                'COL-0580',
                'thomason-trobaugh-localization',
                'AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient.fineTelescopeComparison_stable',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterFineTelescope',
                'k-theory-schemes',
            ),
        ]
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier, section, primary, module, folder in expected:
            item = self.library["entries"][identifier]
            self.assertEqual(item["section"], section)
            self.assertEqual(item["path"], f"docs/library/entries/{folder}/{identifier}.toml")
            self.assertEqual(item["primary"], primary)
            self.assertEqual(built["declarations"][primary]["module"], module)


    def test_iterated_twisted_items_keep_native_owners(self):
        expected = [
            (
                'COL-0581',
                'bass-delooping-normalization-and-telescopes',
                'KTheory.Bass.strictDiagramCofiberComparison_desc',
                'Colib.KTheory.Bass.StrictDiagramCofiberDescent',
                'k-theory',
            ),
            (
                'COL-0582',
                'thomason-trobaugh-localization',
                'KTheory.Bass.GeometricChiPermutation.comparison',
                'Colib.AlgebraicGeometry.KTheory.Bass.GeometricChiPermutation',
                'k-theory-schemes',
            ),
            (
                'COL-0583',
                'thomason-trobaugh-localization',
                'KTheory.Bass.SchemeIteratedSeedTransition.seed_cone_rotation',
                'Colib.AlgebraicGeometry.KTheory.Bass.SchemeSeedRotation',
                'k-theory-schemes',
            ),
            (
                'COL-0584',
                'thomason-trobaugh-localization',
                'KTheory.Bass.SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable',
                'Colib.AlgebraicGeometry.KTheory.Bass.SchemeIteratedSeedTelescope',
                'k-theory-schemes',
            ),
            (
                'COL-0585',
                'thomason-trobaugh-localization',
                'AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull.iterated_twisted_lift_stable_iff',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterIteratedTwistedFiber',
                'k-theory-schemes',
            ),
        ]
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier, section, primary, module, folder in expected:
            item = self.library["entries"][identifier]
            self.assertEqual(item["section"], section)
            self.assertEqual(item["path"], f"docs/library/entries/{folder}/{identifier}.toml")
            self.assertEqual(item["primary"], primary)
            self.assertEqual(built["declarations"][primary]["module"], module)


    def test_auxiliary_current_localization_keeps_three_chapters_and_native_owners(self):
        expected = [
            (
                'COL-0586',
                'bass-delooping-normalization-and-telescopes',
                'KTheory.Bass.StrictDiagramIndexRowMap.telescopeMap_stable',
                'Colib.KTheory.Bass.StrictDiagramIndexRowMapTelescopeNaturality',
                'k-theory',
            ),
            (
                'COL-0587',
                'bass-delooping-diagrams-and-functoriality',
                'KTheory.Bass.LaurentSeed.ModelAction.seedDiagramNull',
                'Colib.RingTheory.KTheory.Bass.StrictLaurentSeedContraction',
                'k-theory',
            ),
            (
                'COL-0588',
                'thomason-trobaugh-localization',
                'AlgebraicGeometry.Scheme.Modules.boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenConeMap_isStableEquivalence',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFiberBassTelescope',
                'k-theory-schemes',
            ),
            (
                'COL-0589',
                'thomason-trobaugh-localization',
                'AlgebraicGeometry.Scheme.Modules.boundedAboveFlatCoefficientSupportedOpenModel_KZero_exact',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenKZeroExact',
                'k-theory-schemes',
            ),
            (
                'COL-0590',
                'thomason-trobaugh-localization',
                'AlgebraicGeometry.Scheme.Modules.boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap_isStableEquivalence',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFullOpenBassLocalization',
                'k-theory-schemes',
            ),
            (
                'COL-0591',
                'thomason-trobaugh-localization',
                'AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient.fiberTelescopeComparison_stable',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterTelescopeComparison',
                'k-theory-schemes',
            ),
            (
                'COL-0592',
                'thomason-trobaugh-localization',
                'AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryCurrentFiber.currentLift_integer_isStableEquivalence',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryCurrentLocalization',
                'k-theory-schemes',
            ),
        ]
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier, section, primary, module, folder in expected:
            item = self.library["entries"][identifier]
            self.assertEqual(item["section"], section)
            self.assertEqual(item["path"], f"docs/library/entries/{folder}/{identifier}.toml")
            self.assertEqual(item["primary"], primary)
            self.assertEqual(built["declarations"][primary]["module"], module)


    def test_ordinary_current_localization_keeps_native_maps_and_scheme_owner(self):
        expected = [
            (
                'COL-0593',
                'thomason-trobaugh-localization',
                'AlgebraicGeometry.Scheme.Modules.boundedAboveFlatCoefficientSupportedBassTelescopeOpenConeMap_isStableEquivalence',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedBassTelescope',
                'k-theory-schemes',
            ),
            (
                'COL-0594',
                'thomason-trobaugh-localization',
                'AlgebraicGeometry.Scheme.Modules.boundedAboveFlatCoefficientOpenModel_KZero_exact',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenKZeroExact',
                'k-theory-schemes',
            ),
            (
                'COL-0595',
                'thomason-trobaugh-localization',
                'AlgebraicGeometry.Scheme.Modules.boundedAboveFlatCoefficientOpenBassTelescopeRestriction_isStableEquivalence',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenRestrictionStable',
                'k-theory-schemes',
            ),
            (
                'COL-0596',
                'thomason-trobaugh-localization',
                'AlgebraicGeometry.Scheme.Modules.boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenFiberMap_isStableEquivalence',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientFullOpenBassLocalization',
                'k-theory-schemes',
            ),
            (
                'COL-0597',
                'thomason-trobaugh-localization',
                'AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient.telescope_fullNull_fine_square',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterTelescopeNull',
                'k-theory-schemes',
            ),
            (
                'COL-0598',
                'thomason-trobaugh-localization',
                'AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull.currentLift_integer_isStableEquivalence',
                'Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterCurrentFullFiber',
                'k-theory-schemes',
            ),
        ]
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier, section, primary, module, folder in expected:
            item = self.library["entries"][identifier]
            self.assertEqual(item["section"], section)
            self.assertEqual(item["path"], f"docs/library/entries/{folder}/{identifier}.toml")
            self.assertEqual(item["primary"], primary)
            self.assertEqual(built["declarations"][primary]["module"], module)

if __name__ == "__main__":
    unittest.main()

