import PfaffianDescent.OneDimensionalQuotientNormalization
import PfaffianDescent.ActualOriginalAllSingleSupportCotangentLine
import PfaffianDescent.ActualOriginalPositiveTwoKernelEmbeddedClassification

/-! SOURCE ONLY / UNVERIFIED. The manuscript's arbitrary one-dimensional
quotient target is normalized internally. ALL supplied actual embedded
rank-eight singleton-support schemes retain their original immersion and
internally derived dual presentation. This depends on unverified existing
all-Z and embedded-kernel prerequisites; it grants no acceptance. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

section
variable {K : Type u} [Field K] [PerfectField K]
  (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
  (P : closedPoints (hypersurface p hp))
  (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)

def actualOriginalPositiveTwoArbitraryTargetJetEmbedding
    {N : Type u} [AddCommGroup N] [Module ((hypersurface p hp).residueField P.1) N]
    (hN : Module.finrank ((hypersurface p hp).residueField P.1) N = 1)
    (q : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1] N) :
    Spec (.of (DualNumber ((hypersurface p hp).residueField P.1))) ⟶ hypersurface p hp :=
  actualOriginalPositiveTwoNativeJetEmbedding p hp P hP
    (normalizeOneDimensionalQuotient hN q)

/-- The forward construction remains a true closed rank-eight subscheme
of the same surface at the same original point. -/
theorem actualOriginalPositiveTwoArbitraryTargetJetEmbedding_actual_tangent
    {N : Type u} [AddCommGroup N] [Module ((hypersurface p hp).residueField P.1) N]
    (hN : Module.finrank ((hypersurface p hp).residueField P.1) N = 1)
    (q : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1] N)
    (hq : Function.Surjective q) :
    let d := actualOriginalPositiveTwoArbitraryTargetJetEmbedding p hp P hP hN q
    IsClosedImmersion d ∧ ∃ hf : IsFinite (d ≫ hypersurfaceToBase p hp),
      Set.range d = {P.1} ∧
        @AllCharacteristics.finiteSchemeRank K _ _ (d ≫ hypersurfaceToBase p hp) hf = 8 :=
  actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP
    (normalizeOneDimensionalQuotient hN q)
    (normalizeOneDimensionalQuotient_surjective hN q hq)

/-- Source isomorphism over the ORIGINAL surface is equivalent to an
isomorphism of the two ACTUAL arbitrary target lines carrying q₁ to q₂. -/
theorem actualOriginalPositiveTwoArbitraryTargetJetEmbedding_overIso_iff
    {N₁ N₂ : Type u} [AddCommGroup N₁]
    [Module ((hypersurface p hp).residueField P.1) N₁]
    [AddCommGroup N₂] [Module ((hypersurface p hp).residueField P.1) N₂]
    (hN₁ : Module.finrank ((hypersurface p hp).residueField P.1) N₁ = 1)
    (hN₂ : Module.finrank ((hypersurface p hp).residueField P.1) N₂ = 1)
    (q₁ : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1] N₁)
    (q₂ : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1] N₂)
    (hq₁ : Function.Surjective q₁) (hq₂ : Function.Surjective q₂) :
    (∃ e : Spec (.of (DualNumber ((hypersurface p hp).residueField P.1))) ≅
        Spec (.of (DualNumber ((hypersurface p hp).residueField P.1))),
      e.hom ≫ actualOriginalPositiveTwoArbitraryTargetJetEmbedding p hp P hP hN₂ q₂ =
        actualOriginalPositiveTwoArbitraryTargetJetEmbedding p hp P hP hN₁ q₁) ↔
      ∃ t : N₁ ≃ₗ[(hypersurface p hp).residueField P.1] N₂,
        q₂ = t.toLinearMap.comp q₁ := by
  exact (actualOriginalPositiveTwoNativeJetEmbedding_overIso_iff_targetIso p hp P hP
    (normalizeOneDimensionalQuotient hN₁ q₁) (normalizeOneDimensionalQuotient hN₂ q₂)
    (normalizeOneDimensionalQuotient_surjective hN₁ q₁ hq₁)
    (normalizeOneDimensionalQuotient_surjective hN₂ q₂ hq₂)).trans
      (normalizedOneDimensionalQuotients_targetIso_iff hN₁ hN₂ q₁ q₂)

/-- Recover a quotient onto ANY actual target line from the SAME supplied
closed immersion, deriving the presentation and quotient internally. -/
theorem actualOriginal_allSingleSupport_rankEight_arbitraryTarget
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hSupport : Set.range i = {P.1})
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ hypersurfaceToBase p hp) = 8)
    {N : Type u} [AddCommGroup N] [Module ((hypersurface p hp).residueField P.1) N]
    (hN : Module.finrank ((hypersurface p hp).residueField P.1) N = 1) :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    ∃ e : Γ(Z, ⊤) ≃ₐ[K] DualNumber ((hypersurface p hp).residueField P.1),
      ∃ q : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1] N,
        Function.Surjective q ∧
        actualOriginalPositiveTwoArbitraryTargetJetEmbedding p hp P hP hN q =
          Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Z.isoSpec.inv ≫ i := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  obtain ⟨e, ell, hell, hemb⟩ :=
    actualOriginal_allSingleSupport_rankEight_cotangentLine p hp P hP i hSupport hZ
  let t := oneDimensionalTargetEquivField ((hypersurface p hp).residueField P.1) N hN
  let q := t.symm.toLinearMap.comp ell
  refine ⟨e, q, t.symm.surjective.comp hell, ?_⟩
  change actualOriginalPositiveTwoNativeJetEmbedding p hp P hP
    (normalizeOneDimensionalQuotient hN q) = _
  have hnorm : normalizeOneDimensionalQuotient hN q = ell :=
    normalizeOneDimensionalQuotient_reverse hN ell
  rw [hnorm]
  exact hemb

end
end PfaffianDescent
