import PfaffianDescent.CorayPlaneCubicJacobianSmooth
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Tactic.FinCases

/-! SOURCE ONLY174. A genuine native Kähler basis on the actual Jacobian
localization of a normalized plane cubic chart. No canonical-module,
residue-generator or perfect-pairing certificate is supplied. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u

/-- The unused original coordinate is complementary to the normalization,
chosen derivative coordinate, and adjoined inverse variable. -/
theorem threeCoordinate_oneFree_complement174
    (i j k : Fin 3) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    IsCompl (Set.range (fun _ : Unit => (Sum.inr k : Unit ⊕ Fin 3)))
      (Set.range (Sum.elim (fun _ : Unit => (Sum.inl () : Unit ⊕ Fin 3))
        (fun a : Fin 2 => Sum.inr (plane_hypersurfaceChartRelationVariables i j a)))) := by
  constructor
  · rw [Set.disjoint_left]
    rintro z ⟨_, rfl⟩ ⟨a, ha⟩
    rcases a with a | a
    · cases ha
    · fin_cases a <;> simp_all
  · rw [codisjoint_iff_le_sup]
    intro z hz
    change z ∈ Set.range (fun _ : Unit => (Sum.inr k : Unit ⊕ Fin 3)) ∪
      Set.range (Sum.elim (fun _ : Unit => (Sum.inl () : Unit ⊕ Fin 3))
        (fun a : Fin 2 => Sum.inr (plane_hypersurfaceChartRelationVariables i j a)))
    rcases z with a | a
    · right
      exact ⟨Sum.inl a, by cases a; rfl⟩
    · have hcover : a = k ∨ a = i ∨ a = j := by
        fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases a <;> simp_all
      rcases hcover with rfl | rfl | rfl
      · left
        exact ⟨(), rfl⟩
      · right
        exact ⟨Sum.inr 0, by simp⟩
      · right
        exact ⟨Sum.inr 1, by simp⟩

section ActualChart
variable {K : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (p : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 3)
variable (i j : Fin 3) (hij : i ≠ j)
noncomputable local instance nativePlaneChartAlgebra174 :
    Algebra K (ChartRing (equationIdeal p hp) j) :=
  (chartBaseMap (equationIdeal p hp) j).toAlgebra

/-- The precise actual open: the Jacobian is the original chosen partial,
by plane_hypersurfaceChartPrePresentation_jacobian. -/
abbrev planeChartJacobianResidueRing174 :=
  Localization.Away (plane_hypersurfaceChartPrePresentation p hp i j hij).jacobian

/-- The actual presentation's complement, with the original coordinates. -/
theorem planeChartJacobianPresentation_complement174
    (k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j) :
    IsCompl (Set.range (fun _ : Unit => (Sum.inr k : Unit ⊕ Fin 3)))
      (Set.range (jacobianLocalizedPresentation
        (plane_hypersurfaceChartPrePresentation p hp i j hij)).map) := by
  change IsCompl (Set.range (fun _ : Unit => (Sum.inr k : Unit ⊕ Fin 3)))
    (Set.range (Sum.elim (fun _ : Unit => (Sum.inl () : Unit ⊕ Fin 3))
      (fun a : Fin 2 => Sum.inr (plane_hypersurfaceChartRelationVariables i j a))))
  exact threeCoordinate_oneFree_complement174 i j k hij hki hkj

/-- A unit-indexed native basis constructed by the actual submersive
presentation. Its vector is the differential of the remaining coordinate. -/
def planeChartJacobianCoordinateDifferentialBasis174
    (k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j) :
    Module.Basis Unit (planeChartJacobianResidueRing174 p hp i j hij)
      (KaehlerDifferential K (planeChartJacobianResidueRing174 p hp i j hij)) :=
  (jacobianLocalizedPresentation
    (plane_hypersurfaceChartPrePresentation p hp i j hij)).basisKaehlerOfIsCompl
      (fun _ _ _ => Subsingleton.elim _ _)
      (planeChartJacobianPresentation_complement174 p hp i j hij k hki hkj)

theorem planeChartJacobianCoordinateDifferentialBasis_apply174
    (k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j) :
    planeChartJacobianCoordinateDifferentialBasis174 p hp i j hij k hki hkj () =
      KaehlerDifferential.D K (planeChartJacobianResidueRing174 p hp i j hij)
        (algebraMap (ChartRing (equationIdeal p hp) j)
          (planeChartJacobianResidueRing174 p hp i j hij)
          (chartCoordinate (equationIdeal p hp) j k)) := by
  let P := jacobianLocalizedPresentation
    (plane_hypersurfaceChartPrePresentation p hp i j hij)
  have hb := P.basisKaehlerOfIsCompl_apply
    (f := fun _ : Unit => (Sum.inr k : Unit ⊕ Fin 3))
    (fun _ _ _ => Subsingleton.elim _ _)
    (planeChartJacobianPresentation_complement174 p hp i j hij k hki hkj) ()
  refine hb.trans ?_
  apply congrArg (KaehlerDifferential.D K (planeChartJacobianResidueRing174 p hp i j hij))
  change algebraMap (ChartRing (equationIdeal p hp) j)
    (planeChartJacobianResidueRing174 p hp i j hij)
    (plane_hypersurfaceChartRelationsEquiv p hp j (Ideal.Quotient.mk _ (X k))) = _
  exact congrArg
    (algebraMap (ChartRing (equationIdeal p hp) j)
      (planeChartJacobianResidueRing174 p hp i j hij))
    ((plane_hypersurfaceChartRelationsEquiv_mk p hp j (X k)).trans
      (MvPolynomial.eval₂_X _ _ k))

/-- The inverted chosen partial's unit is constructed from the actual
localization; it is not supplied by a smoothness or residue certificate. -/
def planeChartJacobianPartialUnit174 :
    (planeChartJacobianResidueRing174 p hp i j hij)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (plane_hypersurfaceChartPrePresentation p hp i j hij).jacobian).unit

/-- This unit is exactly the original chosen partial in the actual chart. -/
theorem planeChartJacobianPartialUnit_val174 :
    (planeChartJacobianPartialUnit174 p hp i j hij :
      planeChartJacobianResidueRing174 p hp i j hij) =
      algebraMap (ChartRing (equationIdeal p hp) j)
        (planeChartJacobianResidueRing174 p hp i j hij)
        (plane_chartPDeriv p hp j ⟨i, hij⟩) := by
  rw [planeChartJacobianPartialUnit174, IsUnit.unit_spec]
  exact congrArg
    (algebraMap (ChartRing (equationIdeal p hp) j)
      (planeChartJacobianResidueRing174 p hp i j hij))
    (plane_hypersurfaceChartPrePresentation_jacobian p hp i j hij)

/-- Scaling the actual coordinate basis by the inverse chosen partial gives
a genuine local residue basis of the SAME native Kähler module. -/
def planeChartJacobianResidueBasis174
    (k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j) :
    Module.Basis Unit (planeChartJacobianResidueRing174 p hp i j hij)
      (KaehlerDifferential K (planeChartJacobianResidueRing174 p hp i j hij)) :=
  (planeChartJacobianCoordinateDifferentialBasis174 p hp i j hij k hki hkj).unitsSMul
    (fun _ => (planeChartJacobianPartialUnit174 p hp i j hij)⁻¹)

theorem planeChartJacobianResidueBasis_apply174
    (k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j) :
    planeChartJacobianResidueBasis174 p hp i j hij k hki hkj () =
      ((planeChartJacobianPartialUnit174 p hp i j hij)⁻¹ :
        (planeChartJacobianResidueRing174 p hp i j hij)ˣ) •
      KaehlerDifferential.D K (planeChartJacobianResidueRing174 p hp i j hij)
        (algebraMap (ChartRing (equationIdeal p hp) j)
          (planeChartJacobianResidueRing174 p hp i j hij)
          (chartCoordinate (equationIdeal p hp) j k)) := by
  rw [planeChartJacobianResidueBasis174, Module.Basis.unitsSMul_apply,
    planeChartJacobianCoordinateDifferentialBasis_apply174]

end ActualChart
end PfaffianDescent.Coray
