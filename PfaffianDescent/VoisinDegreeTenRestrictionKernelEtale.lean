import PfaffianDescent.TripleCompleteIntersectionEtaleRegularity
import PfaffianDescent.VoisinRestrictionKernelEtale
import PfaffianDescent.VoisinDegreeTenSmoothStart

/-!
# Restriction-kernel endpoint for Voisin's degree-ten residual

This file joins the restriction-kernel étale selector to the concrete
degree-ten residual construction.  Once the actual singular parameter locus
is proper, the rank-sixteen completion makes the selected étale intersection
nonempty.  Proper étaleness makes it finite, and finite nonempty intersection
of three positive-degree forms makes the third equation regular modulo the
first two.  The existing complete-intersection argument then produces the
finite étale rank-eleven residual.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite-subscheme datum of positive rank has a nonempty underlying
closed subscheme. -/
theorem finiteSubschemeDatum_subscheme_nonempty_of_pos
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    {n : ℕ} (D : FiniteSubschemeDatum f n) (hn : 0 < n) :
    Nonempty D.val.subscheme := by
  letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ f)
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ f)
  have hfinrank : Module.finrank K Γ(D.val.subscheme, ⊤) = n :=
    (finiteSchemeCoefficient_finrank (D.val.subschemeι ≫ f)).trans
      ((finiteSchemeRank_eq_finrank (D.val.subschemeι ≫ f)).trans
        (D.property.2.2.2 (IsLocalRing.closedPoint K)))
  haveI : Nontrivial Γ(D.val.subscheme, ⊤) :=
    Module.nontrivial_of_finrank_pos (hfinrank ▸ hn)
  exact Nonempty.map D.val.subscheme.isoSpec.inv inferInstance

/-- A normalized chart of the rank-sixteen completion on which the actual
restriction-kernel singular parameter locus is proper.  This packages the
remaining geometric condition together with the chart already used to embed
the completion. -/
def DegreeTenRegularCubicSectionRestrictionKernelProperChart
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀) : Prop :=
  let D := S.completion.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∃ (z : CoordinateRing (equationIdeal p hp))
    (hz : z ∈ grading (equationIdeal p hp) 1)
    (x : Fin 4 → Γ(D.val.subscheme, ⊤))
    (he : ∀ s ∈ (equationIdeal p hp).toIdeal,
      (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) s = 0)
    (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) he) z = 1),
    Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
    S.q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
    linearNormalizedPointAt (equationIdeal p hp) x he z hz hzOne =
      D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ∧
    tripleCompleteIntersectionRestrictionKernelSingularParameterLocus
      p S.q hp S.hq x ≠ Set.univ

/-- An étale third cubic through the positive-rank completion is automatically
regular modulo the first two cubics.  This is the prime-free selected Bertini
interface used by the restriction-kernel construction. -/
noncomputable def
    DegreeTenRegularCubicSectionSelectedThirdCubicData.ofChartEtale
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 3)
    (chart : DegreeTenRegularCubicSectionSelectedThirdCubicChart
      p hp D₁₀ S r)
    (hetale : Etale
      (toBase (tripleCompleteIntersectionHomogeneousIdeal
        p S.q r hp S.hq hr))) :
    DegreeTenRegularCubicSectionSelectedThirdCubicData p hp D₁₀ S := by
  let D := S.completion.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  let I := tripleCompleteIntersectionHomogeneousIdeal p S.q r hp S.hq hr
  let j : D.val.subscheme ⟶ scheme I :=
    finiteSubschemeDatumCompleteIntersectionEmbeddingOfNormalizedChart
      p S.q r hp S.hq hr 16 D chart
  have hD : Nonempty D.val.subscheme :=
    finiteSubschemeDatum_subscheme_nonempty_of_pos
      (hypersurfaceToBase p hp) D (by norm_num)
  have hX : Nonempty (scheme I) := Nonempty.map j hD
  exact {
    r := r
    hr := hr
    regular := fun F hF =>
      tripleCompleteIntersection_third_regular_of_etale_of_nonempty
        p S.q r hp S.hq hr (by norm_num) hetale hX F hF
    chart := chart
    transverse := hetale }

/-- Properness of the actual restriction-kernel singular locus selects a
third cubic over the ground field.  The selected nonempty étale intersection
itself forces the third cubic to be regular modulo the first two. -/
theorem
    nonempty_degreeTenRegularCubicSectionSelectedThirdCubicData_of_restrictionKernelProperChart
    {K : Type u} [Field K] [Infinite K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hproper :
      DegreeTenRegularCubicSectionRestrictionKernelProperChart p hp D₁₀ S) :
    Nonempty (DegreeTenRegularCubicSectionSelectedThirdCubicData p hp D₁₀ S) := by
  let D := S.completion.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI : Module.Finite K Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hpoint, hsing⟩ := hproper
  obtain ⟨i, g, _hgbase, _hr0, hrvan, hetale⟩ :=
    exists_groundFieldRestrictionKernel_parameterChart_etale_of_singularLocus_ne_univ
      p S.q hp S.hq x hsing
  let r := cubicRestrictionKernelSpecializedCubic (K := K) x i g
  let hr := cubicRestrictionKernelSpecializedCubic_isHomogeneous (K := K) x i g
  have chart :
      DegreeTenRegularCubicSectionSelectedThirdCubicChart p hp D₁₀ S r := by
    exact ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hrvan, hpoint⟩
  exact ⟨DegreeTenRegularCubicSectionSelectedThirdCubicData.ofChartEtale
    p hp D₁₀ S r hr chart hetale⟩

/-- The direct degree-ten endpoint of the restriction-kernel construction:
properness of the singular parameter locus gives a disjoint finite étale
residual of rank eleven. -/
theorem
    exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_restrictionKernelProperChart
    {K : Type u} [Field K] [Infinite K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hproper :
      DegreeTenRegularCubicSectionRestrictionKernelProperChart p hp D₁₀ S) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp)
          S.completion.datum))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  obtain ⟨T⟩ :=
    nonempty_degreeTenRegularCubicSectionSelectedThirdCubicData_of_restrictionKernelProperChart
      p hp D₁₀ S hproper
  exact exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_selectedThirdCubicData
    p hp hp0 D₁₀ S T

end PfaffianDescent
