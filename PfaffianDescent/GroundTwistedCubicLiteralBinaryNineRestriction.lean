import PfaffianDescent.GroundTwistedCubicNativeCoordinateImages
import PfaffianDescent.GroundTwistedCubicCubicIntersectionAnyField

/-! SOURCE ONLY. Literal degree-nine restriction and WHOLE equation-ideal
image under the SAME chosen ground polynomial parametrization. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped MatrixGroups
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- The EXACT polynomial substitution selected by the EXISTING original
ground scheme parametrization: same Classical.choose matrix, standard
cubic parametrization, and canonical Fin2-to-Bool rename. -/
def GroundTwistedCubicPresentation.literalBinaryParameterHom
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B) :
    MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial Bool K :=
  let A : GL (Fin 4) K := Classical.choose hB
  (rename finTwoEquiv).comp
    ((standardTwistedCubicParam K).comp (linearSubstitution (A : Matrix (Fin 4) (Fin 4) K)))

/-- Its four coordinate polynomials are the VERY SAME cubics in the
checked original native whole-coordinate image law. -/
theorem GroundTwistedCubicPresentation.literalBinaryParameterHom_X
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B) (i : Fin 4) :
    hB.literalBinaryParameterHom (X i) =
      (standardTwistedCubicLiteralLineLinearPolynomial (K := K)
        ((Classical.choose hB : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i :
          MvPolynomial Bool K) := by
  simp only [GroundTwistedCubicPresentation.literalBinaryParameterHom,
    AlgHom.comp_apply, linearSubstitution_X]
  rfl

/-- The ORIGINAL cubic becomes a literal homogeneous binary degree-nine
polynomial. Neither degree nine nor a target polynomial is an input. -/
def GroundTwistedCubicPresentation.literalRestrictedBinaryNine
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) : homogeneousSubmodule Bool K 9 :=
  ⟨hB.literalBinaryParameterHom F, by
    let A : GL (Fin 4) K := Classical.choose hB
    change (rename finTwoEquiv
      (standardTwistedCubicParam K
        (linearSubstitution (A : Matrix (Fin 4) (Fin 4) K) F))).IsHomogeneous 9
    have h := (standardTwistedCubicParam_homogeneous
      (linearSubstitution_homogeneous (A : Matrix (Fin 4) (Fin 4) K) hF)).rename_isHomogeneous (f := finTwoEquiv)
    simpa only [Nat.reduceMul] using h⟩

/-- Vanishing of the SAME restricted polynomial is exactly containment
of the ORIGINAL cubic in the ORIGINAL whole ground curve ideal. -/
theorem GroundTwistedCubicPresentation.literalRestrictedBinaryNine_zero_iff
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    (hB.literalRestrictedBinaryNine F hF : MvPolynomial Bool K) = 0 ↔ F ∈ B.toIdeal := by
  let A : GL (Fin 4) K := Classical.choose hB
  have hA := Classical.choose_spec hB
  have h := twisted_cubic_mem_iff_transformed_param_zero B A hA F
  change rename finTwoEquiv
    (standardTwistedCubicParam K (linearSubstitution (A : Matrix (Fin 4) (Fin 4) K) F)) = 0 ↔ _
  exact (rename_eq_zero_iff_of_injective _ finTwoEquiv.injective).trans h.symm

/-- Noncontainment DERIVES actual nonzero degree nine, not merely an
upper degree bound or an assumed Bézout/rank certificate. -/
theorem GroundTwistedCubicPresentation.literalRestrictedBinaryNine_nonzero_degree
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hnot : F ∉ B.toIdeal) :
    (hB.literalRestrictedBinaryNine F hF : MvPolynomial Bool K) ≠ 0 ∧
      (hB.literalRestrictedBinaryNine F hF : MvPolynomial Bool K).totalDegree = 9 := by
  have hn : (hB.literalRestrictedBinaryNine F hF : MvPolynomial Bool K) ≠ 0 := by
    intro hz
    exact hnot ((hB.literalRestrictedBinaryNine_zero_iff F hF).mp hz)
  exact ⟨hn, (hB.literalRestrictedBinaryNine F hF).property.totalDegree hn⟩

/-- Map of a kernel ideal is zero, proved before actual polynomial
rings or the original chosen ground matrix are substituted. -/
private theorem ringHom_map_kernel_botCut
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (RingHom.ker f).map f = ⊥ := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    exact le_rfl
  · exact bot_le

private theorem originalGroundCurve_binaryIdealImage_botCut
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B) :
    B.toIdeal.map hB.literalBinaryParameterHom.toRingHom = ⊥ := by
  let A : GL (Fin 4) K := Classical.choose hB
  have hA := Classical.choose_spec hB
  have hstd : (standardTwistedCubicIdeal K).map (standardTwistedCubicParam K).toRingHom = ⊥ := by
    rw [standardTwistedCubicIdeal_eq_ker]
    exact ringHom_map_kernel_botCut _
  change B.toIdeal.map ((rename finTwoEquiv).toRingHom.comp
    ((standardTwistedCubicParam K).toRingHom.comp
      (linearSubstitution (A : Matrix (Fin 4) (Fin 4) K)).toRingHom)) = ⊥
  rw [← Ideal.map_map, ← Ideal.map_map, hA, hstd, Ideal.map_bot]

/-- The ENTIRE original summed intersection ideal, with all multiplicity
and nilpotent equations retained, maps to the literal binary equation
ideal under the SAME polynomial parametrization; no radicals or supports. -/
theorem GroundTwistedCubicPresentation.wholeIntersection_binaryEquationIdeal_image
    {B : HomogeneousIdeal PS} (hB : GroundTwistedCubicPresentation B)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    (groundTwistedCubicCubicIntersectionIdeal B F hF).toIdeal.map
        hB.literalBinaryParameterHom.toRingHom =
      (equationIdeal (hB.literalRestrictedBinaryNine F hF : MvPolynomial Bool K)
        (hB.literalRestrictedBinaryNine F hF).property).toIdeal := by
  change (B.toIdeal ⊔ Ideal.span {F}).map hB.literalBinaryParameterHom.toRingHom =
    Ideal.span {hB.literalBinaryParameterHom F}
  rw [Ideal.map_sup, originalGroundCurve_binaryIdealImage_botCut hB,
    bot_sup_eq, Ideal.map_span, Set.image_singleton]
  rfl

end PfaffianDescent.QuarticNet
