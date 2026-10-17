import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualIdempotentLength
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

noncomputable section
open AlgebraicGeometry CategoryTheory Module
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_openClosed_kernel_idempotent
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsAffine X]
    [IsClosedImmersion i] [IsOpenImmersion i] :
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧
      RingHom.ker i.appTop.hom = Ideal.span {e} := by
  letI : IsAffine Z := isAffine_of_isAffineHom i
  have h : Spec.map i.appTop = Z.isoSpec.inv ≫ i ≫ X.isoSpec.hom := by
    apply (cancel_mono X.isoSpec.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact Scheme.isoSpec_inv_naturality i
  letI : IsOpenImmersion (Spec.map i.appTop) := by
    rw [h]
    infer_instance
  exact (isOpenImmersion_SpecMap_iff_of_surjective i.appTop
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2).mp inferInstance

theorem cubicClosedPointSerreFiniteZeroResidual_openClosed_rank_complement
    {K : Type u} [Field K] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsOpenImmersion i]
    (f : X ⟶ Spec (.of K)) [IsFinite f] (N d : ℕ)
    (hX : AllCharacteristics.finiteSchemeRank f = N)
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ f) = d) :
    AllCharacteristics.finiteSchemeRank (finiteClosedResidualι i f ≫ f) = N - d := by
  letI := finiteSchemeCoefficientAlgebra f
  letI := finiteSchemeCoefficientAlgebra (i ≫ f)
  have := finiteSchemeCoefficient_finite f
  have := finiteSchemeCoefficient_finite (i ≫ f)
  letI : IsAffine X := isAffine_of_isAffineHom f
  obtain ⟨e, he, hP⟩ :=
    cubicClosedPointSerreFiniteZeroResidual_openClosed_kernel_idempotent i
  let P := RingHom.ker i.appTop.hom
  have hA : finrank K Γ(X, ⊤) = N := (finiteSchemeCoefficient_finrank f).trans hX
  have hQ : finrank K (Γ(X, ⊤) ⧸ P) = d := by
    have hg := (Ideal.quotientKerAlgEquivOfSurjective
      (finiteSchemeClosedMap_surjective i f)).toLinearEquiv.finrank_eq
    exact hg.trans ((finiteSchemeCoefficient_finrank (i ≫ f)).trans hZ)
  have hcomp : finiteClosedResidualι i f ≫ f =
      residualAffineι P ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤))) := by
    rw [finiteSchemeCoefficient_spec f]
    exact Category.assoc _ _ _
  rw [AllCharacteristics.finiteSchemeRank_eq_finrank, hcomp, residualAffineι_toBase,
    Scheme.Hom.finrank_SpecMap_algebraMap]
  refine (congrFun (Module.rankAtStalk_eq_finrank_of_free
    (R := K) (M := Γ(X, ⊤) ⧸ residualAlgebraIdeal P)) _).trans ?_
  change P = Ideal.span {e} at hP
  rw [hP] at hQ ⊢
  exact cubicClosedPointSerreFiniteZeroResidual_idempotent_finrank e he N d hA hQ

end PfaffianDescent
