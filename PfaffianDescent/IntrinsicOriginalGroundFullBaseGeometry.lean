import PfaffianDescent.IntrinsicFullBaseAlternativeSourceIso
import AllCharacteristics.TwistedCubicLemma

/-! Geometry of the actual original full base: its twisted branch contains
the SAME supplied Z as a closed subscheme and is P1 over the ORIGINAL field.
The original ambient map and both structural morphisms are retained. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {k : Type u} [Field k] [PerfectField k]
attribute [local instance] MvPolynomial.gradedAlgebra

def IntrinsicOriginalGroundFullBaseAlternative {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k)) : Prop :=
  let B := intrinsicFullQuadraticBaseIdeal i
  (∃ l : Z ⟶ scheme B, IsIso l ∧ l ≫ quotientProjMap B = i) ∨
    QuarticNet.GroundTwistedCubicPresentation B ∧
    (∃ l : Z ⟶ scheme B, IsClosedImmersion l ∧
      l ≫ quotientProjMap B = i ∧ l ≫ toBase B = i ≫ ambientToBase) ∧
    (∃ e : scheme B ≅ projectiveLineProj k,
      e.hom ≫ projectiveLineProjToBase k = toBase B ∧
      Smooth (toBase B) ∧ ∃ s : Spec (.of k) ⟶ scheme B, s ≫ toBase B = 𝟙 _)

/-- Auxiliary branch assembly: the branch's actual twisted presentation
supplies curve geometry; full intrinsic kernel containment supplies its
closed original-Z embedding. No embedding or equation comparison is input. -/
theorem intrinsicOriginalTwistedFullBase_geometry {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k)) [IsClosedImmersion i]
    (hTwisted : QuarticNet.GroundTwistedCubicPresentation (intrinsicFullQuadraticBaseIdeal i)) :
    let B := intrinsicFullQuadraticBaseIdeal i
    QuarticNet.GroundTwistedCubicPresentation B ∧
    (∃ l : Z ⟶ scheme B, IsClosedImmersion l ∧
      l ≫ quotientProjMap B = i ∧ l ≫ toBase B = i ≫ ambientToBase) ∧
    (∃ e : scheme B ≅ projectiveLineProj k,
      e.hom ≫ projectiveLineProjToBase k = toBase B ∧
      Smooth (toBase B) ∧ ∃ s : Spec (.of k) ⟶ scheme B, s ≫ toBase B = 𝟙 _) := by
  let B := intrinsicFullQuadraticBaseIdeal i
  let l := IsClosedImmersion.lift (quotientProjMap B) i
    (intrinsicFullQuadraticBaseIdeal_ker_le i)
  have hfac : l ≫ quotientProjMap B = i := IsClosedImmersion.lift_fac _ _ _
  letI : IsClosedImmersion (l ≫ quotientProjMap B) := by rw [hfac]; infer_instance
  have hl : IsClosedImmersion l := IsClosedImmersion.of_comp l (quotientProjMap B)
  have hbase : l ≫ toBase B = i ≫ ambientToBase := by
    rw [← quotientProjMap_toBase, ← Category.assoc, hfac]
  exact ⟨hTwisted, ⟨l, hl, hfac, hbase⟩,
    hTwisted.schemeIsoProjectiveLine, hTwisted.schemeIsoProjectiveLine_hom_toBase,
    hTwisted.toBase_smooth,
    QuarticNet.geometricallyStandardTwistedCubic_has_rational_section
      (AllCharacteristics.groundTwistedCubicPresentation_geometricallyStandard hTwisted)⟩

end PfaffianDescent
