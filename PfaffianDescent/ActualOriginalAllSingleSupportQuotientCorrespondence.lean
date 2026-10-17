import PfaffianDescent.ActualOriginalAllSingleSupportCotangentLine
import PfaffianDescent.ActualOriginalPositiveTwoKernelEmbeddedClassification
import PfaffianDescent.ActualOriginalPositiveTwoNativeJetGeometricSplitting
import PfaffianDescent.SingleSupportGeometricSchemeSplitting

/-! SOURCE ONLY / UNVERIFIED. Quotient classes of the genuine original
Omega(2) fiber correspond to classes of ALL actual rank-eight closed
subschemes supported at the given quartic point. Subscheme equivalence
is an actual source isomorphism commuting with the original immersion.
The inverse retains the exact supplied i and its internally derived e. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

structure ActualOriginalRankEightEmbeddedJet
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp)) where
  carrier : Scheme.{u}
  immersion : carrier ⟶ hypersurface p hp
  closed : IsClosedImmersion immersion
  finite : IsFinite (immersion ≫ hypersurfaceToBase p hp)
  support : Set.range immersion = {P.1}
  rank : @AllCharacteristics.finiteSchemeRank K _ _
    (immersion ≫ hypersurfaceToBase p hp) finite = 8

def actualOriginalRankEightEmbeddedJetSetoid
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp)) :
    Setoid (ActualOriginalRankEightEmbeddedJet p hp P) where
  r A B := ∃ e : A.carrier ≅ B.carrier, e.hom ≫ B.immersion = A.immersion
  iseqv :=
    { refl := fun A => ⟨Iso.refl A.carrier, by simp⟩
      symm := by
        rintro A B ⟨e, he⟩
        refine ⟨e.symm, ?_⟩
        change e.inv ≫ A.immersion = B.immersion
        rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
      trans := by
        rintro A B C ⟨eAB, hAB⟩ ⟨eBC, hBC⟩
        refine ⟨eAB ≪≫ eBC, ?_⟩
        change (eAB.hom ≫ eBC.hom) ≫ C.immersion = A.immersion
        rw [Category.assoc, hBC, hAB] }

abbrev ActualOriginalRankEightEmbeddedJetClasses
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp)) :=
  Quotient (actualOriginalRankEightEmbeddedJetSetoid p hp P)

abbrev ActualOriginalPositiveTwoQuotientClasses
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp)) :=
  Quotient (surjectiveOneDimensionalQuotientSetoid
    ((hypersurface p hp).residueField P.1) (ActualOriginalPositiveTwoFiber p hp P))

section
variable {K : Type u} [Field K] [PerfectField K]
  (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
  (P : closedPoints (hypersurface p hp))
  (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4)

def actualOriginalRankEightEmbeddedJetOfImmersion
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hSupport : Set.range i = {P.1})
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ hypersurfaceToBase p hp) = 8) :
    ActualOriginalRankEightEmbeddedJet p hp P where
  carrier := Z
  immersion := i
  closed := inferInstance
  finite := inferInstance
  support := hSupport
  rank := hZ

def actualOriginalRankEightEmbeddedJetOfQuotient
    (ell : {ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
      (hypersurface p hp).residueField P.1 // Function.Surjective ell}) :
    ActualOriginalRankEightEmbeddedJet p hp P := by
  let h := actualOriginalPositiveTwoNativeJetEmbedding_actual_tangent p hp P hP ell.1 ell.2
  exact
    { carrier := Spec (.of (DualNumber ((hypersurface p hp).residueField P.1)))
      immersion := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell.1
      closed := h.1
      finite := Classical.choose h.2
      support := (Classical.choose_spec h.2).1
      rank := (Classical.choose_spec h.2).2 }

include hP in
theorem actualOriginalRankEightEmbeddedJets_geometric_split
    (A : ActualOriginalRankEightEmbeddedJet p hp P) :
    ∃ (J : Type u) (_ : Fintype J), Fintype.card J = 4 ∧
      Nonempty (pullback
        (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
        (A.immersion ≫ hypersurfaceToBase p hp) ≅
          ∐ fun _ : J => Spec (.of (DualNumber (AlgebraicClosure K)))) := by
  letI : IsClosedImmersion A.immersion := A.closed
  letI : IsFinite (A.immersion ≫ hypersurfaceToBase p hp) := A.finite
  exact singleClosedSupport_actual_geometric_scheme_splits (K := AlgebraicClosure K)
    A.immersion (hypersurfaceToBase p hp) P A.support hP A.rank

def actualOriginalPositiveTwoQuotientToEmbeddedJetClasses :
    ActualOriginalPositiveTwoQuotientClasses p hp P →
      ActualOriginalRankEightEmbeddedJetClasses p hp P :=
  Quotient.map (actualOriginalRankEightEmbeddedJetOfQuotient p hp P hP)
    (by
      intro ell₁ ell₂ h
      change ∃ e : Spec (.of (DualNumber ((hypersurface p hp).residueField P.1))) ≅
          Spec (.of (DualNumber ((hypersurface p hp).residueField P.1))),
        e.hom ≫ actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell₂.1 =
          actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell₁.1
      exact (actualOriginalPositiveTwoNativeJetEmbedding_overIso_iff_targetIso
        p hp P hP ell₁.1 ell₂.1 ell₁.2 ell₂.2).mpr h)

theorem actualOriginalPositiveTwoQuotientToEmbeddedJetClasses_injective :
    Function.Injective (actualOriginalPositiveTwoQuotientToEmbeddedJetClasses p hp P hP) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro ell₁ ell₂ h
  change Quotient.mk (actualOriginalRankEightEmbeddedJetSetoid p hp P)
      (actualOriginalRankEightEmbeddedJetOfQuotient p hp P hP ell₁) =
    Quotient.mk (actualOriginalRankEightEmbeddedJetSetoid p hp P)
      (actualOriginalRankEightEmbeddedJetOfQuotient p hp P hP ell₂) at h
  apply Quotient.sound
  exact (actualOriginalPositiveTwoNativeJetEmbedding_overIso_iff_targetIso
    p hp P hP ell₁.1 ell₂.1 ell₁.2 ell₂.2).mp (Quotient.exact h)

theorem actualOriginalPositiveTwoQuotientToEmbeddedJetClasses_surjective :
    Function.Surjective (actualOriginalPositiveTwoQuotientToEmbeddedJetClasses p hp P hP) := by
  intro a
  refine Quotient.inductionOn a ?_
  intro A
  letI : IsClosedImmersion A.immersion := A.closed
  letI : IsFinite (A.immersion ≫ hypersurfaceToBase p hp) := A.finite
  letI : IsAffine A.carrier := isAffine_of_isAffineHom (A.immersion ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra (A.immersion ≫ hypersurfaceToBase p hp)
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  obtain ⟨e, ell, hell, hemb⟩ :=
    actualOriginal_allSingleSupport_rankEight_cotangentLine p hp P hP A.immersion A.support A.rank
  refine ⟨Quotient.mk _ ⟨ell, hell⟩, ?_⟩
  change Quotient.mk (actualOriginalRankEightEmbeddedJetSetoid p hp P)
      (actualOriginalRankEightEmbeddedJetOfQuotient p hp P hP ⟨ell, hell⟩) =
    Quotient.mk (actualOriginalRankEightEmbeddedJetSetoid p hp P) A
  apply Quotient.sound
  change ∃ eSpec : Spec (.of (DualNumber ((hypersurface p hp).residueField P.1))) ≅ A.carrier,
    eSpec.hom ≫ A.immersion = actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
  refine ⟨Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op ≪≫ A.carrier.isoSpec.symm, ?_⟩
  change (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ A.carrier.isoSpec.inv) ≫ A.immersion = _
  simpa only [Category.assoc] using hemb.symm

def actualOriginalAllSingleSupportQuotientCorrespondence :
    ActualOriginalPositiveTwoQuotientClasses p hp P ≃
      ActualOriginalRankEightEmbeddedJetClasses p hp P :=
  Equiv.ofBijective (actualOriginalPositiveTwoQuotientToEmbeddedJetClasses p hp P hP)
    ⟨actualOriginalPositiveTwoQuotientToEmbeddedJetClasses_injective p hp P hP,
      actualOriginalPositiveTwoQuotientToEmbeddedJetClasses_surjective p hp P hP⟩

theorem actualOriginalAllSingleSupportQuotientCorrespondence_inverse_given_immersion
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hSupport : Set.range i = {P.1})
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ hypersurfaceToBase p hp) = 8) :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    ∃ e : Γ(Z, ⊤) ≃ₐ[K] DualNumber ((hypersurface p hp).residueField P.1),
      ∃ ell : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
          (hypersurface p hp).residueField P.1,
        ∃ hell : Function.Surjective ell,
          actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell =
            Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Z.isoSpec.inv ≫ i ∧
          (actualOriginalAllSingleSupportQuotientCorrespondence p hp P hP).symm
            (Quotient.mk _ (actualOriginalRankEightEmbeddedJetOfImmersion
              p hp P i hSupport hZ)) = Quotient.mk _ ⟨ell, hell⟩ := by
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  obtain ⟨e, ell, hell, hemb⟩ :=
    actualOriginal_allSingleSupport_rankEight_cotangentLine p hp P hP i hSupport hZ
  refine ⟨e, ell, hell, hemb, ?_⟩
  let E := actualOriginalAllSingleSupportQuotientCorrespondence p hp P hP
  have hForward : E (Quotient.mk _ ⟨ell, hell⟩) =
      Quotient.mk _ (actualOriginalRankEightEmbeddedJetOfImmersion p hp P i hSupport hZ) := by
    change Quotient.mk (actualOriginalRankEightEmbeddedJetSetoid p hp P)
        (actualOriginalRankEightEmbeddedJetOfQuotient p hp P hP ⟨ell, hell⟩) =
      Quotient.mk (actualOriginalRankEightEmbeddedJetSetoid p hp P)
        (actualOriginalRankEightEmbeddedJetOfImmersion p hp P i hSupport hZ)
    apply Quotient.sound
    change ∃ eSpec : Spec (.of (DualNumber ((hypersurface p hp).residueField P.1))) ≅ Z,
      eSpec.hom ≫ i = actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell
    refine ⟨Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op ≪≫ Z.isoSpec.symm, ?_⟩
    change (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Z.isoSpec.inv) ≫ i = _
    simpa only [Category.assoc] using hemb.symm
  have hInverse := congrArg E.symm hForward
  rw [E.symm_apply_apply] at hInverse
  exact hInverse.symm

theorem actualOriginal_allSingleSupport_two_immersions_targetIso_classification
    {Z₁ Z₂ : Scheme.{u}} (i₁ : Z₁ ⟶ hypersurface p hp) (i₂ : Z₂ ⟶ hypersurface p hp)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    [IsFinite (i₁ ≫ hypersurfaceToBase p hp)] [IsFinite (i₂ ≫ hypersurfaceToBase p hp)]
    (hSupport₁ : Set.range i₁ = {P.1}) (hSupport₂ : Set.range i₂ = {P.1})
    (hZ₁ : AllCharacteristics.finiteSchemeRank (i₁ ≫ hypersurfaceToBase p hp) = 8)
    (hZ₂ : AllCharacteristics.finiteSchemeRank (i₂ ≫ hypersurfaceToBase p hp) = 8) :
    letI : IsAffine Z₁ := isAffine_of_isAffineHom (i₁ ≫ hypersurfaceToBase p hp)
    letI : IsAffine Z₂ := isAffine_of_isAffineHom (i₂ ≫ hypersurfaceToBase p hp)
    letI := finiteSchemeCoefficientAlgebra (i₁ ≫ hypersurfaceToBase p hp)
    letI := finiteSchemeCoefficientAlgebra (i₂ ≫ hypersurfaceToBase p hp)
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    ∃ (e₁ : Γ(Z₁, ⊤) ≃ₐ[K] DualNumber ((hypersurface p hp).residueField P.1))
      (e₂ : Γ(Z₂, ⊤) ≃ₐ[K] DualNumber ((hypersurface p hp).residueField P.1)),
      ∃ ell₁ ell₂ : ActualOriginalPositiveTwoFiber p hp P →ₗ[(hypersurface p hp).residueField P.1]
        (hypersurface p hp).residueField P.1,
        Function.Surjective ell₁ ∧ Function.Surjective ell₂ ∧
        actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell₁ =
          Spec.map (CommRingCat.ofHom e₁.toRingHom) ≫ Z₁.isoSpec.inv ≫ i₁ ∧
        actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell₂ =
          Spec.map (CommRingCat.ofHom e₂.toRingHom) ≫ Z₂.isoSpec.inv ≫ i₂ ∧
        ((∃ e : Z₁ ≅ Z₂, e.hom ≫ i₂ = i₁) ↔
          OneDimensionalQuotientTargetIso ell₁ ell₂) := by
  letI : IsAffine Z₁ := isAffine_of_isAffineHom (i₁ ≫ hypersurfaceToBase p hp)
  letI : IsAffine Z₂ := isAffine_of_isAffineHom (i₂ ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra (i₁ ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra (i₂ ≫ hypersurfaceToBase p hp)
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  obtain ⟨e₁, ell₁, hell₁, h₁⟩ :=
    actualOriginal_allSingleSupport_rankEight_cotangentLine p hp P hP i₁ hSupport₁ hZ₁
  obtain ⟨e₂, ell₂, hell₂, h₂⟩ :=
    actualOriginal_allSingleSupport_rankEight_cotangentLine p hp P hP i₂ hSupport₂ hZ₂
  let C₁ := Scheme.Spec.mapIso e₁.toRingEquiv.toCommRingCatIso.op ≪≫ Z₁.isoSpec.symm
  let C₂ := Scheme.Spec.mapIso e₂.toRingEquiv.toCommRingCatIso.op ≪≫ Z₂.isoSpec.symm
  let d₁ := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell₁
  let d₂ := actualOriginalPositiveTwoNativeJetEmbedding p hp P hP ell₂
  have hc₁ : C₁.hom ≫ i₁ = d₁ := by
    change (Spec.map (CommRingCat.ofHom e₁.toRingHom) ≫ Z₁.isoSpec.inv) ≫ i₁ = _
    simpa only [Category.assoc] using h₁.symm
  have hc₂ : C₂.hom ≫ i₂ = d₂ := by
    change (Spec.map (CommRingCat.ofHom e₂.toRingHom) ≫ Z₂.isoSpec.inv) ≫ i₂ = _
    simpa only [Category.assoc] using h₂.symm
  have hi₁ : C₁.inv ≫ d₁ = i₁ := by
    rw [← hc₁, ← Category.assoc, C₁.inv_hom_id, Category.id_comp]
  have hi₂ : C₂.inv ≫ d₂ = i₂ := by
    rw [← hc₂, ← Category.assoc, C₂.inv_hom_id, Category.id_comp]
  refine ⟨e₁, e₂, ell₁, ell₂, hell₁, hell₂, h₁, h₂, ?_⟩
  rw [← actualOriginalPositiveTwoNativeJetEmbedding_overIso_iff_targetIso
    p hp P hP ell₁ ell₂ hell₁ hell₂]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨C₁ ≪≫ e ≪≫ C₂.symm, ?_⟩
    change (C₁.hom ≫ e.hom ≫ C₂.inv) ≫ d₂ = d₁
    simp only [Category.assoc]
    rw [hi₂, he, hc₁]
  · rintro ⟨e, he⟩
    refine ⟨C₁.symm ≪≫ e ≪≫ C₂, ?_⟩
    change (C₁.inv ≫ e.hom ≫ C₂.hom) ≫ i₂ = i₁
    simp only [Category.assoc]
    rw [hc₂, he, hi₁]

end
end PfaffianDescent
