import AllCharacteristics.FiniteFieldPointResidueEmbedding

/-! SOURCE ONLY / UNVERIFIED. The literal finite-field-point cycle is
[M:κ(y)] [y], defined by the full scheme residue degree. Its degree is the
actual coefficient degree, without any separability assumption. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory IsLocalRing
universe u
variable {K M : Type u} [Field K] [Field M] [Algebra K M] [Module.Finite K M]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
variable (a : Spec (.of M) ⟶ X)
variable (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K M)))

def finiteFieldPointExplicitCycle : EffectiveZeroCycle X :=
  Finsupp.single (finiteFieldPointClosedPoint f a ha) (a.residueDegree (closedPoint M))

theorem finiteFieldPoint_residueDegree_eq_finrank :
    letI := (fieldPointResidueRingHom a).toAlgebra
    a.residueDegree (closedPoint M) =
      Module.finrank (X.residueField (a (closedPoint M))) M := by
  let x := closedPoint M
  let c := (a.residueFieldMap x).hom
  letI := c.toAlgebra
  letI := (fieldPointResidueRingHom a).toAlgebra
  let e : (Spec (.of M)).residueField x ≃ₐ[X.residueField (a x)] M :=
    { specFieldClosedPointResidueIso M with commutes' := fun r => rfl }
  exact e.toLinearEquiv.finrank_eq

theorem finiteFieldPointExplicitCycle_eq_single :
    letI := (fieldPointResidueRingHom a).toAlgebra
    finiteFieldPointExplicitCycle f a ha =
      Finsupp.single (finiteFieldPointClosedPoint f a ha)
        (Module.finrank (X.residueField (a (closedPoint M))) M) := by
  unfold finiteFieldPointExplicitCycle
  rw [finiteFieldPoint_residueDegree_eq_finrank a]

theorem finiteFieldPointExplicitCycle_degree :
    EffectiveZeroCycle.degree f (finiteFieldPointExplicitCycle f a ha) =
      Module.finrank K M := by
  haveI : IsFinite (a ≫ f) := by
    rw [ha]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  letI : IsFinite a := IsFinite.of_comp a f
  let cM : closedPoints (Spec (.of M)) :=
    ⟨closedPoint M, IsLocalRing.isClosed_singleton_closedPoint M⟩
  have hpush : pushforwardCycle a (Finsupp.single cM 1) =
      finiteFieldPointExplicitCycle f a ha := by
    unfold pushforwardCycle finiteFieldPointExplicitCycle
    rw [Finsupp.sum_single_index (by simp)]
    simp only [one_mul]
    rfl
  rw [← hpush, degree_pushforwardCycle, ha]
  rw [← fundamentalZeroCycle_Spec_field M cM]
  exact fundamentalZeroCycle_degree_affine

end AllCharacteristics
