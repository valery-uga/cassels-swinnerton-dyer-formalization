import PfaffianDescent.PlaneCubicNativeDifferentialRelation173
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.Ring

/-! SOURCE ONLY173. Actual residue-differential compatibility on the
overlap of the two partial-derivative opens in the SAME original plane
chart. This is not a nonzero global residue or perfect pairing premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u

/-- Pure unit cancellation of the actual cotangent relation. The
geometric caller derives this relation from its own equation below. -/
theorem twoUnitDifferential_residue_sign_overlap173
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (a b : Rˣ) (dx dy : M) (h : (a : R) • dx + (b : R) • dy = 0) :
    ((a⁻¹ : Rˣ) : R) • dy = -(((b⁻¹ : Rˣ) : R) • dx) := by
  have ha : ((((a⁻¹ : Rˣ) : R) * ((b⁻¹ : Rˣ) : R)) * (a : R)) =
      ((b⁻¹ : Rˣ) : R) := by
    calc
      _ = (((a⁻¹ : Rˣ) : R) * (a : R)) * ((b⁻¹ : Rˣ) : R) := by ring
      _ = _ := by simp
  have hb : ((((a⁻¹ : Rˣ) : R) * ((b⁻¹ : Rˣ) : R)) * (b : R)) =
      ((a⁻¹ : Rˣ) : R) := by
    calc
      _ = ((a⁻¹ : Rˣ) : R) * (((b⁻¹ : Rˣ) : R) * (b : R)) := by ring
      _ = _ := by simp
  have hh := congrArg (fun z : M =>
    (((a⁻¹ : Rˣ) : R) * ((b⁻¹ : Rˣ) : R)) • z) h
  rw [smul_add, smul_smul, smul_smul, ha, hb, smul_zero] at hh
  apply eq_neg_iff_add_eq_zero.mpr
  exact (add_comm _ _).trans hh

section ActualChart
variable {K : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (p : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 3) (j : Fin 3)
noncomputable local instance nativePlaneChartAlgebraOverlap173 :
    Algebra K (ChartRing (equationIdeal p hp) j) :=
  (chartBaseMap (equationIdeal p hp) j).toAlgebra

/-- The literal common partial-derivative open, in its actual chart ring.
Both partials become invertible by inverting their product. -/
abbrev planeChartPartialOverlapRing173
    (i k : {a : Fin 3 // a ≠ j}) :=
  Localization.Away (plane_chartPDeriv p hp j i * plane_chartPDeriv p hp j k)

/-- The first partial's actual unit, with explicit inverse b/(ab). -/
def planeChartFirstPartialUnit173
    (i k : {a : Fin 3 // a ≠ j}) : (planeChartPartialOverlapRing173 p hp j i k)ˣ := by
  let B := ChartRing (equationIdeal p hp) j
  let a : B := plane_chartPDeriv p hp j i
  let b : B := plane_chartPDeriv p hp j k
  let R := planeChartPartialOverlapRing173 p hp j i k
  let ai : R := algebraMap B R a
  let bi : R := algebraMap B R b
  let v : R := IsLocalization.Away.invSelf (a * b)
  have hab : ai * (bi * v) = 1 := by
    change algebraMap B R a * (algebraMap B R b *
      IsLocalization.Away.invSelf (a * b)) = 1
    rw [← mul_assoc, ← map_mul, IsLocalization.Away.mul_invSelf]
  exact ⟨ai, bi * v, hab, (mul_comm _ _).trans hab⟩

/-- The second partial's actual unit, with explicit inverse a/(ab). -/
def planeChartSecondPartialUnit173
    (i k : {a : Fin 3 // a ≠ j}) : (planeChartPartialOverlapRing173 p hp j i k)ˣ := by
  let B := ChartRing (equationIdeal p hp) j
  let a : B := plane_chartPDeriv p hp j i
  let b : B := plane_chartPDeriv p hp j k
  let R := planeChartPartialOverlapRing173 p hp j i k
  let ai : R := algebraMap B R a
  let bi : R := algebraMap B R b
  let v : R := IsLocalization.Away.invSelf (a * b)
  have hba : bi * (ai * v) = 1 := by
    calc
      bi * (ai * v) = ai * (bi * v) := by ring
      _ = 1 := by
        change algebraMap B R a * (algebraMap B R b *
          IsLocalization.Away.invSelf (a * b)) = 1
        rw [← mul_assoc, ← map_mul, IsLocalization.Away.mul_invSelf]
  exact ⟨bi, ai * v, hba, (mul_comm _ _).trans hba⟩

/-- Genuine local residue-differential overlap equality in Ω of the
SAME actual product localization. Actual partial units and the native
two-coordinate cotangent relation are derived internally from p and its
chart normalization; no overlap or canonical-module certificate input. -/
theorem planeChart_actualPartialResidue_differential_overlap173
    (i k : {a : Fin 3 // a ≠ j}) (hik : i.1 ≠ k.1) :
    let B := ChartRing (equationIdeal p hp) j
    let R := planeChartPartialOverlapRing173 p hp j i k
    ((planeChartFirstPartialUnit173 p hp j i k)⁻¹ : Rˣ) •
      KaehlerDifferential.D K R (algebraMap B R (chartCoordinate (equationIdeal p hp) j k.1)) =
      -(((planeChartSecondPartialUnit173 p hp j i k)⁻¹ : Rˣ) •
        KaehlerDifferential.D K R (algebraMap B R (chartCoordinate (equationIdeal p hp) j i.1))) := by
  let B := ChartRing (equationIdeal p hp) j
  let R := planeChartPartialOverlapRing173 p hp j i k
  let f : B →ₐ[K] R := IsScalarTower.toAlgHom K B R
  have h := planeChart_nativeKaehler_two_partial_relation173 p hp j f
    i.1 k.1 i.2 k.2 hik
  change (((planeChartFirstPartialUnit173 p hp j i k)⁻¹ : Rˣ) : R) •
      KaehlerDifferential.D K R (algebraMap B R (chartCoordinate (equationIdeal p hp) j k.1)) =
    -((((planeChartSecondPartialUnit173 p hp j i k)⁻¹ : Rˣ) : R) •
      KaehlerDifferential.D K R (algebraMap B R (chartCoordinate (equationIdeal p hp) j i.1)))
  exact twoUnitDifferential_residue_sign_overlap173
    (planeChartFirstPartialUnit173 p hp j i k) (planeChartSecondPartialUnit173 p hp j i k)
    (KaehlerDifferential.D K R (algebraMap B R (chartCoordinate (equationIdeal p hp) j i.1)))
    (KaehlerDifferential.D K R (algebraMap B R (chartCoordinate (equationIdeal p hp) j k.1))) h

end ActualChart
end PfaffianDescent.Coray
