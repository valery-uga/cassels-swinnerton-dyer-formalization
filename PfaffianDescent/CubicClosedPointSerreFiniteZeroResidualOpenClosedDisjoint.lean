import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOpenClosedRank

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_openClosed_disjoint
    {K : Type u} [Field K] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsOpenImmersion i]
    (f : X ⟶ Spec (.of K)) [IsFinite f] :
    Disjoint (Set.range i) (Set.range (finiteClosedResidualι i f)) := by
  letI : IsAffine X := isAffine_of_isAffineHom f
  letI := finiteSchemeCoefficientAlgebra f
  obtain ⟨e, he, hP⟩ :=
    cubicClosedPointSerreFiniteZeroResidual_openClosed_kernel_idempotent i
  let P := RingHom.ker i.appTop.hom
  have htop : P ⊔ residualAlgebraIdeal P = ⊤ := by
    change P = Ideal.span {e} at hP
    rw [hP, residualAlgebraIdeal_span_idempotent e he.eq]
    apply (Ideal.eq_top_iff_one _).mpr
    rw [Submodule.mem_sup]
    exact ⟨e, Ideal.mem_span_singleton_self e, 1 - e,
      Ideal.mem_span_singleton_self (1 - e), by ring⟩
  have hraw : Disjoint
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))))
      (Set.range (residualAffineι P)) :=
    disjoint_range_quotientAffineι_residualAffineι_of_sup_eq_top P htop
  have horig : Set.range i = Set.range
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)) ≫ X.isoSpec.inv) := by
    simpa [P] using range_closedImmersion_eq_range_quotientAffine i
  unfold finiteClosedResidualι
  rw [horig, Set.disjoint_left]
  rintro x ⟨y, hy⟩ ⟨z, hz⟩
  have hinj : Function.Injective X.isoSpec.inv := by
    intro a b hab
    have h := congrArg (fun g => X.isoSpec.hom g) hab
    simpa using h
  apply (Set.disjoint_left.mp hraw) ⟨y, rfl⟩
  refine ⟨z, ?_⟩
  exact hinj (hz.trans hy.symm)

end PfaffianDescent
