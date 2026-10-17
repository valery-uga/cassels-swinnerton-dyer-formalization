import PfaffianDescent.SingleSupportGeometricDualSplitting

/-! Four dual factors of the ACTUAL field-base-changed supplied scheme. The
finite scheme's true affine reconstruction retains its original projection. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] {Z : Scheme.{u}}

/-- Canonical affine presentation of the actual field base change of a finite
scheme, obtained from its real isoSpec and finite coefficient algebra. -/
def finiteSchemeActualFieldBaseChangeIso (t : Z ⟶ Spec (.of k)) [IsFinite t] :
    letI := finiteSchemeCoefficientAlgebra t
    pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) t ≅
      Spec (.of (K ⊗[k] Γ(Z, ⊤))) := by
  letI := finiteSchemeCoefficientAlgebra t
  letI : IsAffine Z := isAffine_of_isAffineHom t
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let c := Spec.map (CommRingCat.ofHom (algebraMap k Γ(Z, ⊤)))
  have ht : t ≫ 𝟙 _ = Z.isoSpec.hom ≫ c := by
    dsimp only [c]
    rw [Category.comp_id, finiteSchemeCoefficient_spec t]
    simp
  exact asIso (pullback.map b t b c (𝟙 _) Z.isoSpec.hom (𝟙 _) (by simp) ht) ≪≫
    pullbackSpecIso k K Γ(Z, ⊤)

/-- The affine tensor presentation retains the projection to the SAME
original scheme Z, not just an abstract scheme isomorphism. -/
theorem finiteSchemeActualFieldBaseChangeIso_hom_toOriginal
    (t : Z ⟶ Spec (.of k)) [IsFinite t] :
    letI := finiteSchemeCoefficientAlgebra t
    letI : IsAffine Z := isAffine_of_isAffineHom t
    (finiteSchemeActualFieldBaseChangeIso (K := K) t).hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : Γ(Z, ⊤) →ₐ[k] (K ⊗[k] Γ(Z, ⊤))).toRingHom) ≫
      Z.isoSpec.inv = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) t := by
  letI := finiteSchemeCoefficientAlgebra t
  letI : IsAffine Z := isAffine_of_isAffineHom t
  dsimp only [finiteSchemeActualFieldBaseChangeIso]
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  erw [pullbackSpecIso_hom_snd_assoc]
  change pullback.lift _ _ _ ≫ pullback.snd _ _ ≫ Z.isoSpec.inv = _
  rw [pullback.lift_snd_assoc]
  simp

/-- Every supplied length-eight scheme supported at a separable quartic
point becomes four dual-number schemes over an algebraically closed field.
Its locality, residue quotient, section and dual description are derived. -/
theorem singleClosedSupport_actual_geometric_scheme_splits
    [PerfectField k] [IsAlgClosed K] {X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsFinite (i ≫ f)]
    (P : closedPoints X) (hSupport : Set.range i = {P.1})
    (hP : f.residueDegree P.1 = 4)
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ f) = 8) :
    ∃ (J : Type u) (_ : Fintype J), Fintype.card J = 4 ∧
      Nonempty (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) (i ≫ f) ≅
        ∐ fun _ : J => Spec (.of (DualNumber K))) := by
  classical
  letI := finiteSchemeCoefficientAlgebra (i ≫ f)
  obtain ⟨J, hJ, hcard, ⟨e⟩⟩ :=
    singleClosedSupport_geometric_globalSpec_splits (K := K) i f P hSupport hP hZ
  letI := hJ
  exact ⟨J, hJ, hcard, ⟨finiteSchemeActualFieldBaseChangeIso (K := K) (i ≫ f) ≪≫ e⟩⟩

end PfaffianDescent
